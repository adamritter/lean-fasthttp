import Std.Internal.UV.TCP
import Std.Http.Protocol.H1

/-! A small callback server: Std's unmodified HTTP/1.1 protocol machine over
Internal.UV, without the stream/channel/select machinery of Std.Http.Server.
Request bodies are buffered, bounded by `Config.protocol.maxBodySize`.
Responses have a fixed, immutable body; streaming, upgrades, TLS, deadlines and
graceful server shutdown are outside this experimental adapter's scope.
-/
namespace FastHTTP.H1

open Std.Http
private abbrev Machine := Protocol.H1.Machine .receiving
private abbrev Socket := Std.Internal.UV.TCP.Socket

structure Request where
  head : Std.Http.Request.Head
  body : ByteArray

/-- Immutable response data, reusable across clients; no consumption cursor. -/
structure Response where
  head : Std.Http.Response.Head
  body : ByteArray

def Response.bytes (body : ByteArray) (status : Status := .ok) : Response :=
  ⟨{ status, headers := .empty |>.insert .contentType (.mk "application/octet-stream") }, body⟩

inductive Reply where
  | ready (response : Response)
  | deferred (response : IO.Promise (Except IO.Error Response))

/-- Runs on a Lean worker. Return promptly; use a deferred reply for async work. -/
abbrev Handler := Request → IO Reply

structure Config where
  protocol : Protocol.H1.Config := {
    maxMessages := 1000000000, maxHeaderBytes := 16384,
    maxHeaderValueLength := 16384, maxBodySize := 1024 * 1024
  }

private def after (promise : IO.Promise (Except IO.Error α))
    (next : Except IO.Error α → IO Unit) : IO Unit := do
  let result := promise.result?
  let deliver := fun value => next (value.getD (.error (IO.userError "dropped IO promise")))
  if ← IO.hasFinished result then deliver result.get
  else IO.chainTask result deliver

private def finish (socket : Socket) : IO Unit := do
  try after (← socket.shutdown) (fun _ => pure ())
  catch _ => pure ()

private structure State where
  machine : Machine
  head : Option Std.Http.Request.Head := none
  body : ByteArray := .empty

private def applyResponse (state : State) (response : Response) : State :=
  let machine := state.machine.setKnownSize (.fixed response.body.size) |>.send response.head
  let machine := if machine.writer.omitBody || response.body.isEmpty then machine
    else machine.sendData #[{ data := response.body }]
  { machine := machine.userClosedBody }

mutual
  private partial def pump (socket : Socket) (handler : Handler) (state : State) : IO Unit := do
    let (machine, step) := state.machine.step
    let state := { state with machine }
    if step.output.isEmpty then
      progress socket handler state step.events
    else
      try
        after (← socket.send step.output.data) fun
          | .ok () => progress socket handler state step.events
          | .error _ => finish socket
      catch _ => finish socket

  private partial def progress (socket : Socket) (handler : Handler) (initial : State)
      (events : Array (Protocol.H1.Event .receiving)) : IO Unit := do
    let mut state := initial
    let mut needsInput := false
    for event in events do
      match event with
      | .endHeaders head => state := { state with head := some head }
      | .needMoreData _ => needsInput := true
      | .«continue» => state := { state with machine := state.machine.canContinue .«continue» }
      | .failed _ | .close => return ← finish socket
      | _ => pure ()
    if state.machine.canPullBodyNow then
      let (machine, pulled) := state.machine.pullBody
      let body := match pulled with
        | none => state.body
        | some p => if state.body.isEmpty then p.chunk.data else state.body ++ p.chunk.data
      pump socket handler { state with machine, body }
    else if let some head := state.head then
      if state.machine.isReaderComplete || state.machine.isReaderClosed then
        try
          match ← handler ⟨head, state.body⟩ with
          | .ready response => pump socket handler (applyResponse state response)
          | .deferred promise =>
            after promise fun
              | .ok response => pump socket handler (applyResponse state response)
              | .error _ => finish socket
        catch _ => finish socket
      else if needsInput || state.machine.pullBodyStalled then
        receive socket handler state
      else pump socket handler state
    else if state.machine.halted then finish socket
    else if needsInput then receive socket handler state
    else pump socket handler state

  private partial def receive (socket : Socket) (handler : Handler) (state : State) : IO Unit := do
    try
      after (← socket.recv? 8192) fun
        | .ok (some bytes) => pump socket handler { state with machine := state.machine.feed bytes }
        | .ok none => pump socket handler { state with machine := state.machine.noMoreInput }
        | .error _ => finish socket
    catch _ => finish socket
end

private partial def acceptNext (server : Socket) (handler : Handler) (config : Config)
    (failed : IO.Promise (Except IO.Error Unit)) : IO Unit := do
  try
    after (← server.accept) fun
      | .error error => failed.resolve (.error error)
      | .ok socket => do
        try
          socket.noDelay
          receive socket handler { machine := { config := config.protocol } }
        catch _ => finish socket
        acceptNext server handler config failed
  catch error => failed.resolve (.error error)

def serve (address : Std.Net.SocketAddress) (handler : Handler) (config : Config := {}) : IO Unit := do
  let server ← Std.Internal.UV.TCP.Socket.new
  server.bind address
  server.listen 1024
  server.noDelay
  let failed ← IO.Promise.new
  acceptNext server handler config failed
  match ← IO.wait failed.result? with
  | some result => IO.ofExcept result
  | none => throw (IO.userError "accept loop stopped")

end FastHTTP.H1
