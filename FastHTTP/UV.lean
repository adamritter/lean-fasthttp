import FastHTTP
import LeanUV

/-! FastHTTP's complete protocol and response API on independent lean-uv workers.
All connection state, handlers, date caches and continuations belong to a worker.
Promises are observed on that worker; no socket escapes to a task-pool callback. -/
namespace FastHTTP.UV

private structure Context where
  handler : Handler
  config : Config
  dates : DateCache
  writeLimit : Nat

private structure Streaming where
  request : Request
  rest : ByteArray
  response : StreamResponse
  control : IO.Ref Protocol.StreamState

private structure Connection where
  socket : LeanUV.TCP.Socket
  state : IO.Ref Protocol.State
  pending : IO.Ref (Option (IO Unit))
  stream : IO.Ref (Option Streaming)
  closed : IO.Ref Bool

private def release (c : Connection) : IO Unit := do
  let active ← c.stream.get
  c.stream.set none
  if let some stream := active then
    let transition := Protocol.streamStep stream.request (← stream.control.get) .closed
    stream.control.set transition.state
    if transition.release then
      try stream.response.release catch _ => pure ()

private def abort (c : Connection) : IO Unit := do
  c.pending.set none
  release c
  c.closed.set true
  c.socket.close

private def finish (c : Connection) : IO Unit := do
  c.closed.set true
  c.pending.set none
  release c
  c.socket.shutdown

private def suspend (c : Connection) (next : IO Unit) : IO Unit := do
  c.socket.pause
  c.pending.set (some next)
  c.socket.setWakeup true

/-- Only one write can be outstanding per connection. A slow reader cannot make
an unbounded producer or pipeline accumulate responses in user-space memory. -/
private def afterWrite (c : Connection) (next : IO Unit) : IO Unit := do
  if (← c.socket.queuedBytes) == 0 then next else suspend c next

private partial def writeLarge (c : Connection) (limit : Nat) (buffers : Array ByteArray)
    (index offset : Nat) (next : IO Unit) : IO Unit := do
  if index >= buffers.size then return ← next
  let bytes := buffers[index]!
  if offset >= bytes.size then return ← writeLarge c limit buffers (index + 1) 0 next
  let stop := min bytes.size (offset + limit)
  c.socket.send (bytes.extract offset stop)
  afterWrite c (writeLarge c limit buffers index stop next)

private def write (c : Connection) (ctx : Context) (buffers : Array ByteArray)
    (next : IO Unit) : IO Unit := do
  let size := buffers.foldl (fun n bytes => n + bytes.size) 0
  if size > ctx.writeLimit then writeLarge c ctx.writeLimit buffers 0 0 next
  else
    c.socket.sendv buffers
    afterWrite c next

private def reject (c : Connection) (ctx : Context) (status : Nat) : IO Unit := do
  let reason := match status with
    | 414 => "URI Too Long" | 413 => "Content Too Large" | 417 => "Expectation Failed"
    | 431 => "Request Header Fields Too Large" | 501 => "Not Implemented"
    | 505 => "HTTP Version Not Supported" | 408 => "Request Timeout"
    | 500 => "Internal Server Error" | _ => "Bad Request"
  let response ← IO.ofExcept ((Response.create .empty status reason).mapError IO.userError)
  write c ctx (response.buffers true false (← ctx.dates.get)) (finish c)

mutual
  private partial def resume (c : Connection) (ctx : Context)
      (request : Request) (rest : ByteArray) (fuel : Nat) : IO Unit := do
    if request.close then finish c
    else if rest.isEmpty then c.state.set (.head)
    else if fuel == 0 then suspend c (process c ctx (Protocol.feed ctx.config (.head) rest) 256)
    else process c ctx (Protocol.feed ctx.config (.head) rest) (fuel - 1)

  private partial def send (c : Connection) (ctx : Context)
      (request : Request) (rest : ByteArray) (response : Response) (fuel : Nat) : IO Unit := do
    write c ctx (response.buffers request.close request.isHead (← ctx.dates.get)
      (request.versionMinor == 0)) (resume c ctx request rest fuel)

  private partial def deferred (c : Connection) (ctx : Context)
      (request : Request) (rest : ByteArray) (promise : IO.Promise (Except IO.Error Response)) : IO Unit := do
    if ← IO.hasFinished promise.result? then
      match promise.result?.get with
      | some (.ok response) => send c ctx request rest response 256
      | _ => reject c ctx 500
    else suspend c (deferred c ctx request rest promise)

  private partial def streamResult (c : Connection) (ctx : Context) (stream : Streaming)
      (promise : IO.Promise (Except IO.Error (Option ByteArray))) (fuel : Nat) : IO Unit := do
    if !(← IO.hasFinished promise.result?) then
      return ← suspend c (streamResult c ctx stream promise 256)
    match promise.result?.get with
    | some (.ok none) => runStream c ctx stream .eof fuel
    | some (.ok (some bytes)) => runStream c ctx stream (.chunk bytes) fuel
    | _ => runStream c ctx stream .failed fuel

  private partial def pullStream (c : Connection) (ctx : Context) (stream : Streaming) (fuel : Nat) : IO Unit := do
    if fuel == 0 then return ← suspend c (pullStream c ctx stream 256)
    streamResult c ctx stream (← stream.response.next) (fuel - 1)

  /-- Commit the proved transition before executing its effects. Wakeups and
  producer completions remain on the socket's owning worker. -/
  private partial def runStream (c : Connection) (ctx : Context) (stream : Streaming)
      (event : Protocol.StreamEvent) (fuel : Nat) : IO Unit := do
    let transition := Protocol.streamStep stream.request (← stream.control.get) event
    stream.control.set transition.state
    if transition.release then
      try stream.response.release catch _ => pure ()
    match transition.command with
    | .idle => pure ()
    | .resume =>
      c.stream.set none
      resume c ctx stream.request stream.rest fuel
    | .finish => finish c
    | .abort => abort c
    | .pull => pullStream c ctx stream fuel
    | .write buffers => write c ctx buffers (runStream c ctx stream .written fuel)

  private partial def process (c : Connection) (ctx : Context)
      (step : Protocol.Step) (fuel : Nat) : IO Unit := do
    match step with
    | .need state => c.state.set state
    | .reject status => reject c ctx status
    | .«continue» state =>
      write c ctx #["HTTP/1.1 100 Continue\r\n\r\n".toUTF8]
        (process c ctx (Protocol.feed ctx.config state .empty) fuel)
    | .request request rest =>
      let reply ← try ctx.handler request catch _ => return ← reject c ctx 500
      match reply with
      | .ready response => send c ctx request rest response fuel
      | .deferred promise => deferred c ctx request rest promise
      | .streaming response =>
        let stream : Streaming := ⟨request, rest, response, ← IO.mkRef {}⟩
        c.stream.set (some stream)
        write c ctx (response.buffers request.close (request.versionMinor == 0) (← ctx.dates.get))
          (runStream c ctx stream .written fuel)

end

/-- Create handlers and mutable application state inside `makeHandler`, once per
worker. The factory itself is shared. The original ready/deferred/streaming API
is preserved; all parsing goes through `Protocol.feed`, including benchmarks. -/
def serve (transport : LeanUV.TCP.Config) (makeHandler : UInt32 → IO Handler)
    (config : Config := {}) : IO (Array LeanUV.TCP.WorkerStats) :=
  LeanUV.TCP.serve transport fun worker => do
    let ctx : Context := ⟨← makeHandler worker, config, ← DateCache.create,
      min transport.maxQueuedBytes.toNat 2147483647⟩
    return fun socket => do
      let c : Connection := ⟨socket, ← IO.mkRef (.head), ← IO.mkRef none,
        ← IO.mkRef none, ← IO.mkRef false⟩
      return {
        onData := fun bytes => do
          try process c ctx (Protocol.feed config (← c.state.get) bytes) 256
          catch _ => abort c
        onWake := do
          if (← socket.queuedBytes) != 0 then return
          let next ← c.pending.get
          c.pending.set none
          socket.setWakeup false
          try
            if let some action := next then action
            if (← c.pending.get).isNone && !(← c.closed.get) then socket.resume
          catch _ => abort c
        onClose := do
          c.closed.set true
          c.pending.set none
          release c }

end FastHTTP.UV
