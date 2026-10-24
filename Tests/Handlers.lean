import FastHTTP

private def prepared (body : String) : IO FastHTTP.Response :=
  IO.ofExcept ((FastHTTP.Response.create body.toUTF8).mapError IO.userError)

namespace Tests

def makeHandler : IO FastHTTP.Handler := do
  let ready ← prepared "ready"
  match FastHTTP.Response.create ByteArray.empty 200 "OK\r\nInjected: yes" with
  | .ok _ => throw (IO.userError "response header injection accepted")
  | .error _ => pure ()
  let released ← IO.mkRef 0
  return fun request => do
    if request.targetIs "/released" then return .ready (← prepared (toString (← released.get)))
    if request.targetIs "/stream-body" then
      let offset ← IO.mkRef 0
      let next := do
        let promise ← IO.Promise.new
        let first ← offset.get
        if first == request.body.size then promise.resolve (.ok none)
        else
          let last := min request.body.size (first + 1024)
          offset.set last
          promise.resolve (.ok (some (request.body.extract first last)))
        return promise
      let response ← IO.ofExcept ((FastHTTP.StreamResponse.create next
        (released.modify (· + 1))).mapError IO.userError)
      return .streaming response
    if request.targetIs "/stream-deferred" then
      let next := do
        let promise ← IO.Promise.new
        let _ ← IO.asTask (prio := .dedicated) do
          IO.sleep 100
          promise.resolve (.ok (some "later".toUTF8))
        return promise
      let response ← IO.ofExcept ((FastHTTP.StreamResponse.create next
        (released.modify (· + 1))).mapError IO.userError)
      return .streaming response
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
    if request.targetIs "/authority" then return .ready (← prepared request.authority)
    if request.targetIs "/request-target" then return .ready (← prepared request.requestTarget)
    if request.targetIs "/raw-trailers" then
      let value := (request.rawTrailers[0]?.map Prod.snd).getD .empty
      return .ready (← IO.ofExcept ((FastHTTP.Response.create value).mapError IO.userError))
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

end Tests
