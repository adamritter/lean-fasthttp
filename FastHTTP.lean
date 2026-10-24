import Std.Internal.UV.TCP
import FastHTTP.Protocol
import FastHTTP.Stream
import FastHTTP.Date

namespace FastHTTP

inductive Reply where
  | ready (response : Response)
  | streaming (response : StreamResponse)
  | deferred (response : IO.Promise (Except IO.Error Response))

/-- Return promptly; deferred replies suspend only their connection. -/
abbrev Handler := Request → IO Reply

/-- One shared context keeps callback captures small and avoids repeatedly
retaining three independent immutable objects at every asynchronous boundary. -/
private structure Context where
  handler : Handler
  config : Config
  dates : DateCache

private abbrev Socket := Std.Internal.UV.TCP.Socket

private def after (promise : IO.Promise (Except IO.Error α))
    (next : Except IO.Error α → IO Unit) : IO Unit := do
  let result := promise.result?
  let deliver := fun value => next (value.getD (.error (IO.userError "dropped IO promise")))
  if ← IO.hasFinished result then deliver result.get
  else IO.chainTask result deliver

private def finish (client : Socket) : IO Unit := do
  try after (← client.shutdown) (fun _ => pure ())
  catch _ => pure ()

private def reject (client : Socket) (ctx : Context) (status : Nat) : IO Unit := do
  let reason := match status with
    | 414 => "URI Too Long" | 413 => "Content Too Large" | 417 => "Expectation Failed"
    | 431 => "Request Header Fields Too Large" | 501 => "Not Implemented"
    | 505 => "HTTP Version Not Supported" | 408 => "Request Timeout"
    | 500 => "Internal Server Error" | _ => "Bad Request"
  match Response.create .empty status reason with
  | .error _ => finish client
  | .ok response =>
    try after (← client.send (response.buffers true false (← ctx.dates.get))) (fun _ => finish client)
    catch _ => finish client

mutual
  private partial def receive (client : Socket) (ctx : Context)
      (state : Protocol.State) : IO Unit := do
    try
      after (← client.recv? 8192) fun
        | .ok (some bytes) => process client ctx (Protocol.feed ctx.config state bytes)
        | _ => finish client
    catch _ => finish client

  private partial def process (client : Socket) (ctx : Context)
      (step : Protocol.Step) : IO Unit := do
    match step with
    | .need state => receive client ctx state
    | .reject status => reject client ctx status
    | .«continue» state =>
      try
        after (← client.send #["HTTP/1.1 100 Continue\r\n\r\n".toUTF8]) fun
          | .ok () => process client ctx (Protocol.feed ctx.config state .empty)
          | .error _ => finish client
      catch _ => finish client
    | .request request rest =>
      try
        match ← ctx.handler request with
        | .ready response => send client ctx request rest response
        | .streaming response =>
          try
            after (← client.send (response.buffers request.close (request.versionMinor == 0) (← ctx.dates.get))) fun
              | .error _ => endStream client response
              | .ok () => do
                if request.isHead then
                  releaseStream response
                  resume client ctx request rest
                else pullStream client ctx request rest response
          catch _ => endStream client response
        | .deferred promise =>
          after promise fun
            | .ok response => send client ctx request rest response
            | .error _ => reject client ctx 500
      catch _ => reject client ctx 500

  private partial def send (client : Socket) (ctx : Context)
      (request : Request) (rest : ByteArray) (response : Response) : IO Unit := do
    try
      after (← client.send (response.buffers request.close request.isHead (← ctx.dates.get) (request.versionMinor == 0))) fun
        | .ok () =>
          resume client ctx request rest
        | .error _ => finish client
    catch _ => finish client

  private partial def resume (client : Socket) (ctx : Context)
      (request : Request) (rest : ByteArray) : IO Unit := do
    if request.close then finish client
    else if rest.isEmpty then receive client ctx (.head)
    else process client ctx (Protocol.feed ctx.config (.head) rest)

  private partial def releaseStream (response : StreamResponse) : IO Unit := do
    try response.release
    catch _ => pure ()

  private partial def endStream (client : Socket) (response : StreamResponse) : IO Unit := do
    releaseStream response
    finish client

  private partial def writeStreamEnd (client : Socket) (ctx : Context)
      (request : Request) (rest : ByteArray) (response : StreamResponse) : IO Unit := do
    releaseStream response
    if request.versionMinor == 0 then return ← finish client
    try
      after (← client.send #["0\r\n\r\n".toUTF8]) fun
        | .ok () => resume client ctx request rest
        | .error _ => finish client
    catch _ => finish client

  private partial def writeStreamChunk (client : Socket) (ctx : Context)
      (request : Request) (rest : ByteArray) (response : StreamResponse) (bytes : ByteArray) : IO Unit := do
    if bytes.isEmpty then return ← endStream client response
    try
      after (← client.send (if request.versionMinor == 0 then #[bytes] else encodeChunk bytes)) fun
        | .ok () => pullStream client ctx request rest response
        | .error _ => endStream client response
    catch _ => endStream client response

  private partial def pullStream (client : Socket) (ctx : Context)
      (request : Request) (rest : ByteArray) (response : StreamResponse) : IO Unit := do
    try
      after (← response.next) fun
        | .error _ => endStream client response
        | .ok none => writeStreamEnd client ctx request rest response
        | .ok (some bytes) => writeStreamChunk client ctx request rest response bytes
    catch _ => endStream client response

end

private partial def acceptNext (server : Socket) (ctx : Context)
    (failed : IO.Promise (Except IO.Error Unit)) : IO Unit := do
  try
    after (← server.accept) fun
      | .error error => failed.resolve (.error error)
      | .ok client => do
        try
          client.noDelay
          receive client ctx (.head)
        catch _ => finish client
        acceptNext server ctx failed
  catch error => failed.resolve (.error error)

def serve (address : Std.Net.SocketAddress) (handler : Handler) (cfg : Config := {}) : IO Unit := do
  let server ← Std.Internal.UV.TCP.Socket.new
  server.bind address
  server.listen 1024
  server.noDelay
  let dates ← DateCache.create
  let ctx : Context := ⟨handler, cfg, dates⟩
  let failed ← IO.Promise.new
  acceptNext server ctx failed
  match ← IO.wait failed.result? with
  | some result => IO.ofExcept result
  | none => throw (IO.userError "accept loop stopped")

end FastHTTP
