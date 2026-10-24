import FastHTTP
import LeanUV.Machine

/-! The complete HTTP connection controller as a pure reactor. Application work,
clock reads and promise polling are explicit commands. The generic lean-uv
adapter commits every state transition before executing its command. -/
namespace FastHTTP
namespace Driver

abbrev ResponsePromise := IO.Promise (Except IO.Error Response)
abbrev ChunkPromise := IO.Promise (Except IO.Error (Option ByteArray))

inductive Work where
  | handle (request : Request)
  | response (promise : ResponsePromise)
  | produce (next : IO ChunkPromise)
  | chunk (promise : ChunkPromise)
  | date
  | release (action : IO Unit)

inductive Result where
  | handled (reply : Reply)
  | response (response : Response)
  | producer (promise : ChunkPromise)
  | chunk (bytes : Option ByteArray)
  | date (bytes : ByteArray)
  | released
  | failed

abbrev Event := LeanUV.TCP.MachineEvent Result
abbrev Command := LeanUV.TCP.MachineCommand Work

inductive Purpose where
  | response (request : Request) (rest : ByteArray)
  | rejection

structure Streaming where
  request : Request
  rest : ByteArray
  response : StreamResponse
  control : Protocol.StreamState := {}

inductive State where
  | reading (parser : Protocol.State := .head)
  | continuing (parser : Protocol.State)
  | handling (request : Request) (rest : ByteArray)
  | preparing (purpose : Purpose) (response : Response)
  | sending (purpose : Purpose)
  | streamDate (stream : Streaming)
  | streaming (stream : Streaming)
  | releasing (next : State) (command : Command)
  | closed

/-- Error responses use the same validated public constructor as application
responses. A construction failure closes the connection without sending bytes. -/
def reject (status : Nat) : State × Command :=
  let reason := match status with
    | 414 => "URI Too Long" | 413 => "Content Too Large" | 417 => "Expectation Failed"
    | 431 => "Request Header Fields Too Large" | 501 => "Not Implemented"
    | 505 => "HTTP Version Not Supported" | 408 => "Request Timeout"
    | 500 => "Internal Server Error" | _ => "Bad Request"
  match Response.create .empty status reason with
  | .error _ => (.closed, .abort)
  | .ok response => (.preparing .rejection response, .perform .date)

/-- Parsing is performed exactly once per input/continuation. A handler command
is emitted only for the complete Request returned by the proved parser. -/
def accept : Protocol.Step → State × Command
  | .need parser => (.reading parser, .idle)
  | .«continue» parser => (.continuing parser, .write #["HTTP/1.1 100 Continue\r\n\r\n".toUTF8])
  | .request request rest => (.handling request rest, .perform (.handle request))
  | .reject status => reject status

def resume (cfg : Config) (purpose : Purpose) : State × Command :=
  match purpose with
  | .rejection => (.closed, .shutdown)
  | .response request rest =>
    if request.close then (.closed, .shutdown)
    else if rest.isEmpty then (.reading, .idle)
    else accept (Protocol.feed cfg .head rest)

def preparedBuffers (purpose : Purpose) (response : Response) (date : ByteArray) : Array ByteArray :=
  match purpose with
  | .rejection => response.buffers true false date
  | .response request _ => response.buffers request.close request.isHead date (request.versionMinor == 0)

/-- Interpret the already-proved stream policy. Cleanup ownership is relinquished
in the pure state before invoking release; the continuation cannot release again. -/
def streamCommand (cfg : Config) (stream : Streaming) : Protocol.StreamCommand → State × Command
  | .idle => (.streaming stream, .idle)
  | .pull => (.streaming stream, .perform (.produce stream.response.next))
  | .write buffers => (.streaming stream, .write buffers)
  | .resume => resume cfg (.response stream.request stream.rest)
  | .finish => (.closed, .shutdown)
  | .abort => (.closed, .abort)

def streamEvent (cfg : Config) (stream : Streaming) (event : Protocol.StreamEvent) : State × Command :=
  let transition := Protocol.streamStep stream.request stream.control event
  let next := streamCommand cfg { stream with control := transition.state } transition.command
  if transition.release then (.releasing next.1 next.2, .finalize (.release stream.response.release)) else next

/-- Interrupting a pending handler or date/write/producer action never dispatches
another request. Any adopted stream is cleaned up before the terminal command. -/
def stop (state : State) (command : Command) : State × Command :=
  match state with
  | .streamDate stream | .streaming stream =>
    if stream.control.ownsResource then
      (.releasing .closed command, .finalize (.release stream.response.release))
    else (.closed, command)
  | _ => (.closed, command)

/-- Total connection transition; scheduling of the matching result/write event
is an explicit generic reactor contract. Unexpected events abort safely. -/
def step (cfg : Config) (state : State) (event : Event) : State × Command :=
  match event with
  | .closed => stop state .idle
  | .failed => stop state .abort
  | _ => match state, event with
    | .reading parser, .data bytes => accept (Protocol.feed cfg parser bytes)
    | .continuing parser, .written => accept (Protocol.feed cfg parser .empty)
    | .handling request rest, .result (.handled reply) => match reply with
      | .ready response => (.preparing (.response request rest) response, .perform .date)
      | .deferred promise => (.handling request rest, .perform (.response promise))
      | .streaming response => (.streamDate ⟨request, rest, response, {}⟩, .perform .date)
    | .handling request rest, .result (.response response) =>
      (.preparing (.response request rest) response, .perform .date)
    | .handling _ _, .result .failed => reject 500
    | .preparing purpose response, .result (.date date) =>
      (.sending purpose, .write (preparedBuffers purpose response date))
    | .sending purpose, .written => resume cfg purpose
    | .streamDate stream, .result (.date date) =>
      (.streaming stream, .write (stream.response.buffers stream.request.close
        (stream.request.versionMinor == 0) date))
    | .streaming stream, .written => streamEvent cfg stream .written
    | .streaming stream, .result (.producer promise) => (.streaming stream, .perform (.chunk promise))
    | .streaming stream, .result (.chunk none) => streamEvent cfg stream .eof
    | .streaming stream, .result (.chunk (some bytes)) => streamEvent cfg stream (.chunk bytes)
    | .streaming stream, .result .failed => streamEvent cfg stream .failed
    | .releasing next command, .result .released => (next, command)
    | .closed, _ => (.closed, .idle)
    | _, _ => stop state .abort

def machine (cfg : Config) : LeanUV.TCP.Machine State Result Work := ⟨.reading, step cfg⟩

/-- This relation specifies only the constructors returned by each external job.
It makes no assumption about HTTP parsing, wire serialization or stream control. -/
def EffectShape : Work → Result → Prop
  | .handle _, .handled _ | .handle _, .failed => True
  | .response _, .response _ | .response _, .failed => True
  | .produce _, .producer _ | .produce _, .failed => True
  | .chunk _, .chunk _ | .chunk _, .failed => True
  | .date, .date _ | .release _, .released => True
  | _, _ => False

end Driver
end FastHTTP
