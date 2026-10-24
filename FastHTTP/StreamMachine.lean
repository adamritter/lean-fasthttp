import FastHTTP.Stream

namespace FastHTTP.Protocol

/-- Protocol states between asynchronous stream callbacks. -/
inductive StreamPhase where
  | headers | producer | chunkWrite | endWrite | done
  deriving BEq, DecidableEq

structure StreamState where
  phase : StreamPhase := .headers
  ownsResource : Bool := true

inductive StreamEvent where
  | written
  | chunk (bytes : ByteArray)
  | eof
  | failed
  | closed

inductive StreamCommand where
  | idle
  | pull
  | write (buffers : Array ByteArray)
  | resume
  | finish
  | abort

structure StreamTransition where
  state : StreamState
  release : Bool := false
  command : StreamCommand := .idle

def streamStop (state : StreamState) (command : StreamCommand) : StreamTransition :=
  ⟨⟨.done, false⟩, state.ownsResource, command⟩

/-- The stream policy executed by both real transports. The interpreter stores
`state` before invoking cleanup or performing the next IO operation. Successful
write completion is the only event that can request another producer chunk. -/
def streamStep (request : Request) (state : StreamState) (event : StreamEvent) : StreamTransition :=
  if state.phase = .done then ⟨state, false, .idle⟩
  else match event with
  | .failed => streamStop state .abort
  | .closed => streamStop state .idle
  | .written => match state.phase with
    | .headers =>
      if request.isHead then streamStop state .resume
      else ⟨{ state with phase := .producer }, false, .pull⟩
    | .chunkWrite => ⟨{ state with phase := .producer }, false, .pull⟩
    | .endWrite => streamStop state .resume
    | _ => ⟨state, false, .idle⟩
  | .eof =>
    if state.phase ≠ .producer then ⟨state, false, .idle⟩
    else if request.versionMinor == 0 then streamStop state .finish
    else ⟨⟨.endWrite, false⟩, state.ownsResource, .write #["0\r\n\r\n".toUTF8]⟩
  | .chunk bytes =>
    if state.phase ≠ .producer then ⟨state, false, .idle⟩
    else if bytes.isEmpty then streamStop state .abort
    else ⟨{ state with phase := .chunkWrite }, false,
      .write (if request.versionMinor == 0 then #[bytes] else encodeChunk bytes)⟩

end FastHTTP.Protocol
