import FastHTTP

private def prepared (body : String) : IO FastHTTP.Response :=
  IO.ofExcept ((FastHTTP.Response.create body.toUTF8).mapError IO.userError)

/-- Separate API regression fixture; not linked into the benchmark executable. -/
def main (args : List String) : IO Unit := do
  let port := (args[0]?.getD "18096").toNat?.getD 18096
  let ready ← prepared "ready"
  match FastHTTP.Response.create ByteArray.empty 200 "OK\r\nInjected: yes" with
  | .ok _ => throw (IO.userError "response header injection accepted")
  | .error _ => pure ()
  let released ← IO.mkRef 0
  FastHTTP.serve (.v4 ⟨.ofParts 127 0 0 1, port.toUInt16⟩) fun request => do
    if request.targetIs "/released" then return .ready (← prepared (toString (← released.get)))
    if request.targetIs "/stream" || request.targetIs "/stream-error" then
      let remaining ← IO.mkRef (if request.targetIs "/stream-error" then 1 else 128)
      let chunk := (String.ofList (List.replicate 65536 's')).toUTF8
      let next := do
        let promise ← IO.Promise.new
        let n ← remaining.get
        if n == 0 then
          if request.targetIs "/stream-error" then promise.resolve (.error (IO.userError "producer error"))
          else promise.resolve (.ok none)
        else
          remaining.set (n - 1)
          promise.resolve (.ok (some chunk))
        return promise
      let response ← IO.ofExcept ((FastHTTP.StreamResponse.create next
        (released.modify (· + 1))).mapError IO.userError)
      return .streaming response
    if request.targetIs "/body" then
      return .ready (← IO.ofExcept ((FastHTTP.Response.create request.body).mapError IO.userError))
    if request.targetIs "/trailers" then
      return .ready (← prepared (String.intercalate ";" (request.trailers.toList.map fun (k,v) => s!"{k}={v}")))
    if request.targetIs "/method" then return .ready (← prepared request.method)
    if request.targetIs "/headers" then
      return .ready (← IO.ofExcept ((FastHTTP.Response.create "headers".toUTF8 200 "OK"
        "text/plain" #[("X-Test", "yes"), ("Set-Cookie", "a=1"), ("Set-Cookie", "b=2")]).mapError IO.userError))
    for status in [204, 205, 304] do
      if request.targetIs s!"/status/{status}" then
        return .ready (← IO.ofExcept ((FastHTTP.Response.create "hidden".toUTF8 status "Test").mapError IO.userError))
    if request.targetIs "/fail" then throw (IO.userError "handler error")
    if request.targetIs "/resolved" then
      let promise ← IO.Promise.new
      promise.resolve (.ok ready)
      return .deferred promise
    if request.targetIs "/deferred" || request.targetIs "/deferred-error" then
      let promise ← IO.Promise.new
      -- Demonstrates completion from an independent producer. Production code
      -- can resolve the promise from another asynchronous I/O callback.
      let _ ← IO.asTask (prio := .dedicated) do
        IO.sleep 250
        if request.targetIs "/deferred-error" then
          promise.resolve (.error (IO.userError "deferred error"))
        else
          promise.resolve (.ok (← prepared (request.header? "x-value" |>.getD "later")))
      return .deferred promise
    if request.targetIs "/echo" then
      return .ready (← prepared s!"{request.method} {request.target} {request.header? "x-value" |>.getD "missing"}")
    return .ready ready
