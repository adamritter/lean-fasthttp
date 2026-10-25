import FastHTTP.Pending
import FastHTTP.AsyncStream
import FastHTTP.SSE

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def raceCase (kind : Nat) : IO Unit := do
  let counts ← Std.Mutex.new (0, 0)
  let release := counts.atomically do modify fun (a, b) => (a + 1, b)
  let cancel := counts.atomically do modify fun (a, b) => (a, b + 1)
  let response ← IO.ofExcept ((FastHTTP.StreamResponse.create
    (throw (IO.userError "unused producer")) release).mapError IO.userError)
  let (pending, resolve) ← FastHTTP.Pending.create cancel
  if kind == 0 then
    pending.cancel
    resolve (.ok (.streaming response))
  else if kind == 1 then
    resolve (.ok (.streaming response))
    pending.cancel
  else if kind == 2 then
    resolve (.ok (.streaming response))
    let some (.ok completion) ← pending.poll | throw (IO.userError "missing completion")
    pending.cancel
    require ((← counts.atomically get) == (0, 0)) "taken result cancelled by gate"
    completion.release
  else
    let first ← IO.asTask (prio := .dedicated) do resolve (.ok (.streaming response))
    let second ← IO.asTask (prio := .dedicated) do
      if kind == 3 then pending.cancel
      else
        if let some (.ok completion) ← pending.poll then completion.release
        pending.cancel
    IO.ofExcept (← IO.wait first)
    IO.ofExcept (← IO.wait second)
  pending.cancel
  require ((← pending.poll).isNone) "gate returned a second completion"
  let (released, cancelled) ← counts.atomically get
  require (released == 1 && cancelled ≤ 1) s!"cleanup counts: {released}, {cancelled}"

def main : IO Unit := do
  for _ in [:100] do
    for kind in [:5] do raceCase kind
  let counts ← Std.Mutex.new 0
  let ctx ← Std.CancellationContext.new
  let headers ← IO.ofExcept ((FastHTTP.StreamResponse.create
    (throw (IO.userError "unattached"))).mapError IO.userError)
  let stream ← FastHTTP.AsyncStream.attach headers {
    next := pure none
    close := counts.atomically do modify (· + 1) } ctx
  let a ← IO.asTask (prio := .dedicated) stream.release
  let b ← IO.asTask (prio := .dedicated) stream.release
  IO.ofExcept (← IO.wait a)
  IO.ofExcept (← IO.wait b)
  require ((← ctx.isCancelled) && (← counts.atomically get) == 1) "stream release race"
  let result ← IO.wait (← stream.next).result?
  require (match result with | some (.error _) => true | _ => false) "cancelled stream pulled producer"
  for value in ["bad\nid", "bad\rid", "bad\x00id"] do
    require (match ({ id := some value } : FastHTTP.SSE.Event).encode with | .error _ => true | _ => false) "SSE id injection"
    require (match ({ event := some value } : FastHTTP.SSE.Event).encode with | .error _ => true | _ => false) "SSE event injection"
  let empty ← IO.ofExcept (({ data := "" } : FastHTTP.SSE.Event).encode.mapError IO.userError)
  require (empty == "data: \n\n".toUTF8) "empty SSE data"
  IO.println "PASS: 500 pending lifecycle cases, concurrent stream release, SSE field validation"
