import FastHTTP.Stream
import Std.Sync.Mutex

namespace FastHTTP

/-- A completed application response; it cannot defer again. -/
inductive Completion where
  | ready (response : Response)
  | streaming (response : StreamResponse)

def Completion.release : Completion → IO Unit
  | .ready _ => pure ()
  | .streaming response => response.release

/-- The gate owns a completed result until the reactor takes it. Closing the
gate releases an unclaimed stream; a late producer releases its own result.
Actions are executed outside the mutex. Resolve exactly once per gate. -/
inductive PendingState (α : Type) where
  | waiting
  | resolved (value : α)
  | closed

def PendingState.resolve (state : PendingState α) (value : α) : PendingState α × Option α :=
  match state with
  | .waiting => (.resolved value, none)
  | _ => (state, some value)

def PendingState.take (state : PendingState α) : PendingState α × Option α :=
  match state with
  | .resolved value => (.closed, some value)
  | _ => (state, none)

def PendingState.close (state : PendingState α) : PendingState α × Option α × Bool :=
  match state with
  | .waiting => (.closed, none, true)
  | .resolved value => (.closed, some value, true)
  | .closed => (.closed, none, false)

structure Pending where
  poll : IO (Option (Except IO.Error Completion))
  cancel : IO Unit
  onReady : IO Unit → IO Unit

/-- Cancellation is cooperative. `cancelWork` must return promptly; it may
signal a cancellation token, but must not wait for the producer to finish. -/
def Pending.create (cancelWork : IO Unit := pure ()) :
    IO (Pending × (Except IO.Error Completion → IO Unit)) := do
  let ready ← IO.Promise.new
  let state ← Std.Mutex.new (PendingState.waiting : PendingState (Except IO.Error Completion))
  let dispose := fun value => do
    if let .ok response := value then
      try response.release catch _ => pure ()
  let poll := state.atomically do
    let (next, value) := (← get).take
    set next
    return value
  let cancel := do
    let (value, notify) ← state.atomically do
      let (next, value, notify) := (← get).close
      set next
      return (value, notify)
    ready.resolve ()
    if notify then
      try cancelWork finally
        if let some value := value then dispose value
  let resolve := fun value => do
    let discard ← state.atomically do
      let (next, discard) := (← get).resolve value
      set next
      return discard
    ready.resolve ()
    if let some value := discard then dispose value
  let onReady : IO Unit → IO Unit := fun notify => BaseIO.chainTask ready.result? fun _ => do
    discard notify.toBaseIO
  return (⟨poll, cancel, onReady⟩, resolve)

end FastHTTP
