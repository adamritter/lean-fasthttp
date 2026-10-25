import FastHTTP.Stream
import Std.Async

namespace FastHTTP.AsyncStream
open Std.Async

/-- Each call supplies one nonempty chunk, or EOF. Check the supplied context
when doing long-running work. `close` must promptly release owned resources. -/
structure Source where
  next : ContextAsync (Option ByteArray)
  close : IO Unit := pure ()

/-- Attach a source to already validated stream headers. Cancellation precedes
cleanup and both happen at most once, even for abandoned asynchronous replies. -/
def attach (headers : StreamResponse) (source : Source) (context : Std.CancellationContext) : IO StreamResponse := do
  let closed ← Std.Mutex.new false
  let release := do
    let first ← closed.atomically do
      let previous ← get
      set true
      return !previous
    if first then
      context.cancel .cancel
      source.close
  let next := do
    let promise ← IO.Promise.new
    let action : Async (Option ByteArray) := do
      if ← context.isCancelled then throw (IO.userError "stream cancelled")
      let chunk ← source.next context
      if ← context.isCancelled then throw (IO.userError "stream cancelled")
      return chunk
    match ← action.toRawBaseIO with
    | .pure value => promise.resolve value
    | .ofTask task => BaseIO.chainTask task promise.resolve
    return promise
  return { headers with next, release }

end FastHTTP.AsyncStream
