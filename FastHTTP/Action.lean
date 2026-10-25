import Std.Async

namespace FastHTTP
open Std.Async

/-- A completed value needs no cancellation scope. Only the scoped branch can
observe a context or wait asynchronously. The caller owns that scope's lifetime. -/
inductive ActionStep (α : Type) where
  | ready (value : α)
  | scoped (run : ContextAsync α)

/-- Request computations with an allocation-free *unused cancellation scope*.
This does not claim that computation, IO, or actual async work is allocation-free.
Run the initial IO promptly on the reactor; use Async for blocking waits. -/
structure Action (α : Type) where
  run : IO (ActionStep α)

namespace Action

def inContext (action : Action α) (context : Std.CancellationContext) : Async α := do
  match ← action.run with
  | .ready value => return value
  | .scoped run => run context

@[inline] protected def pure (value : α) : Action α := ⟨pure (.ready value)⟩

@[inline] def bindStep (step : ActionStep α) (next : α → Action β) : IO (ActionStep β) := do
  match step with
  | .ready value => (next value).run
  | .scoped run => return .scoped fun context => do
      let value ← run context
      (next value).inContext context

@[inline] protected def bind (action : Action α) (next : α → Action β) : Action β :=
  ⟨do bindStep (← action.run) next⟩

instance : Monad Action where
  pure := Action.pure
  bind := Action.bind

@[inline] def ofIO (action : IO α) : Action α := ⟨return .ready (← action)⟩

/-- Inspect the async result once. Already completed tasks can also finish
without a scope; Task.get is used only after hasFinished succeeds. -/
def ofAsync (action : Async α) : Action α := ⟨do
  match ← action.toRawBaseIO with
  | .pure result => return .ready (← IO.ofExcept result)
  | .ofTask task =>
    if ← IO.hasFinished task then return .ready (← IO.ofExcept task.get)
    return .scoped fun _ => EAsync.ofTask task⟩

/-- Explicit compatibility bridge. A ContextAsync computation can observe its
context immediately, so entering this branch necessarily acquires one. -/
def ofContext (action : ContextAsync α) : Action α := ⟨pure (.scoped action)⟩

instance : MonadLift IO Action := ⟨ofIO⟩
instance : MonadLift BaseIO Action := ⟨fun action => ofIO action⟩
instance : MonadLift Async Action := ⟨ofAsync⟩
instance : MonadLift ContextAsync Action := ⟨ofContext⟩

@[inline] protected def throw (error : IO.Error) : Action α := ⟨throw error⟩

def tryCatch (action : Action α) (recover : IO.Error → Action α) : Action α := ⟨do
  try
    match ← action.run with
    | .ready value => return .ready value
    | .scoped run => return .scoped (fun context => do
        try
          run context
        catch error => (recover error).inContext context)
  catch error => (recover error).run⟩

instance : MonadExcept IO.Error Action where
  throw := Action.throw
  tryCatch := Action.tryCatch

def tryFinally' (action : Action α) (cleanup : Option α → Action β) : Action (α × β) := do
  -- Catch only the original computation, never a failure in its cleanup.
  let result ← Action.tryCatch (do return Except.ok (← action))
    (fun error => pure (.error error))
  let cleaned ← cleanup result.toOption
  match result with
  | .ok value => return (value, cleaned)
  | .error error => throw error

instance : MonadFinally Action := ⟨Action.tryFinally'⟩

def getContext : Action Std.CancellationContext := ofContext ContextAsync.getContext
def isCancelled : Action Bool := ofContext ContextAsync.isCancelled
def awaitCancellation : Action Unit := ofContext ContextAsync.awaitCancellation
def cancel (reason : Std.CancellationReason := .cancel) : Action Unit :=
  ofContext (ContextAsync.cancel reason)

end Action
end FastHTTP
