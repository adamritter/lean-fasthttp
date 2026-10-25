import FastHTTP.Batch
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

namespace FastHTTP.AsyncStream
open Std.Async

/-- Coalesce only immediately available chunks. Never wait for another chunk
while bytes are ready to flush. At most `max 1 maxChunks` pulls happen per batch;
the byte limit is checked after each chunk, so an indivisible chunk can exceed it.
One outstanding pull is retained across calls, including a pending failure.
The caller still owns cancellation through the context supplied to `next`. -/
def Source.batchReady (source : Source) (maxChunks : Nat := 32)
    (maxBytes : Nat := 16384) : IO Source := do
  let pending ← IO.mkRef (none : Option (MaybeTask (Except IO.Error (Option ByteArray))))
  let ended ← IO.mkRef false
  return {
    close := do
      pending.set none
      source.close
    next := fun context => do
      if ← context.isCancelled then throw (IO.userError "stream cancelled")
      if ← ended.get then return none
      let mut buffer := ByteArray.empty
      for _ in [:max 1 maxChunks] do
        if ← context.isCancelled then throw (IO.userError "stream cancelled")
        let attempt ← match ← pending.get with
          | some attempt => pure attempt
          | none => liftM (m := BaseIO) (source.next context).toRawBaseIO
        pending.set none
        let result ← match attempt with
          | .pure result => pure result
          | .ofTask task =>
            if ← IO.hasFinished task then pure task.get
            else if !buffer.isEmpty then
              pending.set (some attempt)
              return some buffer
            else
              liftM (m := BaseAsync) (BaseAsync.ofTask task)
        match result with
        | .error error =>
          if buffer.isEmpty then throw error
          pending.set (some (.pure result))
          return some buffer
        | .ok none =>
          ended.set true
          return if buffer.isEmpty then none else some buffer
        | .ok (some bytes) =>
          -- Preserve the original source contract: an empty chunk is invalid,
          -- never silently remove it while coalescing other chunks.
          if bytes.isEmpty then
            if buffer.isEmpty then return some bytes
            pending.set (some (.pure result))
            return some buffer
          buffer := ReadyBatch.append buffer bytes
          if buffer.size ≥ maxBytes then return some buffer
      return some buffer }

end FastHTTP.AsyncStream
