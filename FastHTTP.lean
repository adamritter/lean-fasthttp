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

private def reject (client : Socket) (dates : DateCache) (status : Nat) : IO Unit := do
  let reason := match status with
    | 414 => "URI Too Long" | 413 => "Content Too Large" | 417 => "Expectation Failed"
    | 431 => "Request Header Fields Too Large" | 501 => "Not Implemented"
    | 505 => "HTTP Version Not Supported" | 408 => "Request Timeout"
    | 500 => "Internal Server Error" | _ => "Bad Request"
  match Response.create .empty status reason with
  | .error _ => finish client
  | .ok response =>
    try after (← client.send (response.buffers true false (← dates.get))) (fun _ => finish client)
    catch _ => finish client

mutual
  private partial def receive (client : Socket) (handler : Handler) (cfg : Config) (dates : DateCache)
      (state : Protocol.State) : IO Unit := do
    try
      after (← client.recv? 8192) fun
        | .ok (some bytes) => process client handler cfg dates (Protocol.feed cfg state bytes)
        | _ => finish client
    catch _ => finish client

  private partial def process (client : Socket) (handler : Handler) (cfg : Config) (dates : DateCache)
      (step : Protocol.Step) : IO Unit := do
    match step with
    | .need state => receive client handler cfg dates state
    | .reject status => reject client dates status
    | .«continue» state =>
      try
        after (← client.send #["HTTP/1.1 100 Continue\r\n\r\n".toUTF8]) fun
          | .ok () => process client handler cfg dates (Protocol.feed cfg state .empty)
          | .error _ => finish client
      catch _ => finish client
    | .request request rest =>
      try
        match ← handler request with
        | .ready response => send client handler cfg dates request rest response
        | .streaming response =>
          try
            after (← client.send (response.buffers request.close (request.versionMinor == 0) (← dates.get))) fun
              | .error _ => endStream client response
              | .ok () => do
                if request.isHead then
                  releaseStream response
                  resume client handler cfg dates request rest
                else pullStream client handler cfg dates request rest response
          catch _ => endStream client response
        | .deferred promise =>
          after promise fun
            | .ok response => send client handler cfg dates request rest response
            | .error _ => reject client dates 500
      catch _ => reject client dates 500

  private partial def send (client : Socket) (handler : Handler) (cfg : Config) (dates : DateCache)
      (request : Request) (rest : ByteArray) (response : Response) : IO Unit := do
    try
      after (← client.send (response.buffers request.close request.isHead (← dates.get) (request.versionMinor == 0))) fun
        | .ok () =>
          resume client handler cfg dates request rest
        | .error _ => finish client
    catch _ => finish client

  private partial def resume (client : Socket) (handler : Handler) (cfg : Config) (dates : DateCache)
      (request : Request) (rest : ByteArray) : IO Unit := do
    if request.close then finish client
    else if rest.isEmpty then receive client handler cfg dates (.head)
    else process client handler cfg dates (Protocol.feed cfg (.head) rest)

  private partial def releaseStream (response : StreamResponse) : IO Unit := do
    try response.release
    catch _ => pure ()

  private partial def endStream (client : Socket) (response : StreamResponse) : IO Unit := do
    releaseStream response
    finish client

  private partial def writeStreamEnd (client : Socket) (handler : Handler) (cfg : Config) (dates : DateCache)
      (request : Request) (rest : ByteArray) (response : StreamResponse) : IO Unit := do
    releaseStream response
    if request.versionMinor == 0 then return ← finish client
    try
      after (← client.send #["0\r\n\r\n".toUTF8]) fun
        | .ok () => resume client handler cfg dates request rest
        | .error _ => finish client
    catch _ => finish client

  private partial def writeStreamChunk (client : Socket) (handler : Handler) (cfg : Config) (dates : DateCache)
      (request : Request) (rest : ByteArray) (response : StreamResponse) (bytes : ByteArray) : IO Unit := do
    if bytes.isEmpty then return ← endStream client response
    try
      after (← client.send (if request.versionMinor == 0 then #[bytes] else encodeChunk bytes)) fun
        | .ok () => pullStream client handler cfg dates request rest response
        | .error _ => endStream client response
    catch _ => endStream client response

  private partial def pullStream (client : Socket) (handler : Handler) (cfg : Config) (dates : DateCache)
      (request : Request) (rest : ByteArray) (response : StreamResponse) : IO Unit := do
    try
      after (← response.next) fun
        | .error _ => endStream client response
        | .ok none => writeStreamEnd client handler cfg dates request rest response
        | .ok (some bytes) => writeStreamChunk client handler cfg dates request rest response bytes
    catch _ => endStream client response

end

private partial def acceptNext (server : Socket) (handler : Handler) (cfg : Config) (dates : DateCache)
    (failed : IO.Promise (Except IO.Error Unit)) : IO Unit := do
  try
    after (← server.accept) fun
      | .error error => failed.resolve (.error error)
      | .ok client => do
        try
          client.noDelay
          receive client handler cfg dates (.head)
        catch _ => finish client
        acceptNext server handler cfg dates failed
  catch error => failed.resolve (.error error)

def serve (address : Std.Net.SocketAddress) (handler : Handler) (cfg : Config := {}) : IO Unit := do
  let server ← Std.Internal.UV.TCP.Socket.new
  server.bind address
  server.listen 1024
  server.noDelay
  let dates ← DateCache.create
  let failed ← IO.Promise.new
  acceptNext server handler cfg dates failed
  match ← IO.wait failed.result? with
  | some result => IO.ofExcept result
  | none => throw (IO.userError "accept loop stopped")

end FastHTTP
