import FastHTTP.AsyncStream

namespace FastHTTP.SSE
open Std.Async

structure Event where
  data : String := ""
  event : Option String := none
  id : Option String := none
  retry : Option Nat := none

def singleLine (value : String) : Bool :=
  !value.contains '\r' && !value.contains '\n' && !value.contains '\x00'

/-- Data newlines are represented by repeated data fields; event/id values
cannot inject another field or event. An empty data string is still an event. -/
def Event.encode (value : Event) : Except String ByteArray := do
  let mut text := ""
  if let some event := value.event then
    unless singleLine event do throw "SSE event must be a single line without NUL"
    text := text ++ "event: " ++ event ++ "\n"
  if let some id := value.id then
    unless singleLine id do throw "SSE id must be a single line without NUL"
    text := text ++ "id: " ++ id ++ "\n"
  if let some retry := value.retry then text := text ++ s!"retry: {retry}\n"
  if !value.data.contains '\r' && !value.data.contains '\n' then
    text := text ++ "data: " ++ value.data ++ "\n"
  else
    let normalized := (value.data.replace "\r\n" "\n").replace "\r" "\n"
    for line in normalized.splitOn "\n" do text := text ++ "data: " ++ line ++ "\n"
  return (text ++ "\n").toUTF8

structure Source where
  next : ContextAsync (Option Event)
  close : IO Unit := pure ()

/-- One outstanding application pull survives heartbeat emission. Heartbeats
never start a second pull or drop a pending event. The producer receives the
stream's cancellation context; no task is forcefully terminated. -/
def Source.bytes (source : Source) (heartbeatMs : Nat := 15000) : IO AsyncStream.Source := do
  let pending ← IO.mkRef (none : Option (Task (Except IO.Error (Option Event))))
  let last ← IO.mkRef (← IO.monoMsNow)
  let emit := fun event => do
    last.set (← IO.monoMsNow)
    match event with
    | none => pure none
    | some event => return some (← IO.ofExcept (event.encode.mapError IO.userError))
  let bytes : AsyncStream.Source := {
    close := source.close
    next := fun context => do
      if ← context.isCancelled then throw (IO.userError "SSE cancelled")
      if (← pending.get).isNone then
        let attempt : MaybeTask (Except IO.Error (Option Event)) ←
          liftM (m := BaseIO) (source.next context).toRawBaseIO
        match attempt with
        | .pure result => return ← emit (← IO.ofExcept result)
        | .ofTask task => pending.set (some task)
      let some task ← pending.get | throw (IO.userError "missing SSE producer")
      repeat
        if ← context.isCancelled then throw (IO.userError "SSE cancelled")
        if ← IO.hasFinished task then
          pending.set none
          return ← emit (← IO.ofExcept task.get)
        let now ← IO.monoMsNow
        if heartbeatMs > 0 && now - (← last.get) ≥ heartbeatMs then
          last.set now
          return some ": keep-alive\n\n".toUTF8
        Std.Async.sleep 10
      return none }
  bytes.batchReady

end FastHTTP.SSE
