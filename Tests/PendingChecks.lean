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

private def encoderChecks : IO Unit := do
  let mut samples := [""]
  for _ in [:5] do
    samples := samples.flatMap fun s => ['a', '\r', '\n', 'é', '😀', '\x00'].map (s.push ·)
    for data in samples do
      let normalized := (data.replace "\r\n" "\n").replace "\r" "\n"
      let expected := String.join ((normalized.splitOn "\n").map fun line => "data: " ++ line ++ "\n") ++ "\n"
      let actual ← IO.ofExcept (({ data } : FastHTTP.SSE.Event).encode.mapError IO.userError)
      require (actual == expected.toUTF8) "optimized SSE encoder differs from line-normalizing reference"

private def batchChecks : IO Unit := do
  let ctx ← Std.CancellationContext.new
  let pulls ← IO.mkRef 0
  let promise ← IO.Promise.new
  let source : FastHTTP.AsyncStream.Source := {
    next := fun _ => do
      let n ← pulls.get
      pulls.set (n + 1)
      if n == 0 then return some "first".toUTF8
      if n == 1 then return ← Std.Async.EAsync.ofTask promise.result!
      if n == 2 then return some "third".toUTF8
      return none }
  let batched ← source.batchReady
  match ← (batched.next ctx).toRawBaseIO with
  | .pure (.ok (some bytes)) => require (bytes == "first".toUTF8) "ready bytes changed"
  | _ => throw (IO.userError "batch waited behind an unresolved producer")
  require ((← pulls.get) == 2) "more than one pending pull"
  promise.resolve (.ok (some "second".toUTF8))
  let bytes ← (batched.next ctx).block
  require (bytes == some "secondthird".toUTF8) "pending chunk lost, duplicated or reordered"
  require ((← pulls.get) == 4) "unexpected producer count"
  require ((← (batched.next ctx).block).isNone && (← pulls.get) == 4) "EOF pulled twice"
  -- Fairness and backpressure: never pull an unbounded ready producer.
  for (chunkLimit, byteLimit, expected) in [(3, 1000, 3), (32, 5, 3), (0, 0, 1)] do
    let count ← IO.mkRef 0
    let source : FastHTTP.AsyncStream.Source := { next := fun _ => do
      count.modify (· + 1)
      return some "xx".toUTF8 }
    let source ← source.batchReady chunkLimit byteLimit
    let some bytes ← (source.next ctx).block | throw (IO.userError "missing batch")
    require ((← count.get) == expected && bytes.size == 2 * expected) "batch limit exceeded"
  for invalidEmpty in [false, true] do
    let count ← IO.mkRef 0
    let source : FastHTTP.AsyncStream.Source := { next := fun _ => do
      let n ← count.get
      count.set (n + 1)
      if n == 0 then return some "before".toUTF8
      if invalidEmpty then return some ByteArray.empty
      throw (IO.userError "producer failure") }
    let source ← source.batchReady
    require ((← (source.next ctx).block) == some "before".toUTF8) "discarded bytes before failure"
    match ← (source.next ctx).toRawBaseIO with
    | .pure (.error _) => require (!invalidEmpty) "empty chunk became exception"
    | .pure (.ok (some bytes)) => require (invalidEmpty && bytes.isEmpty) "invalid chunk hidden"
    | _ => throw (IO.userError "pending failure was not preserved")
  ctx.cancel .cancel
  match ← (batched.next ctx).toRawBaseIO with
  | .pure (.error _) => pure ()
  | _ => throw (IO.userError "batch ignored cancellation")

def main : IO Unit := do
  batchChecks
  encoderChecks
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
  IO.println "PASS: 500 pending lifecycle cases, concurrent stream release, SSE field validation, bounded ready-only batching, 9330 SSE encoder cases"
