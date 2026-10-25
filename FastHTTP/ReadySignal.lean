import Std.Async

namespace FastHTTP.ReadySignal
open Std.Async

/-- Pure transitions used under the signal mutex. Exactly one selector may be
registered at a time. Completion remains observable after unregistering. -/
structure State (α : Type) where
  ready : Bool := false
  waiter : Option α := none

def State.register (state : State α) (waiter : α) : State α × Option α :=
  if state.ready then (state, some waiter)
  else ({ state with waiter := some waiter }, none)

def State.finish (state : State α) : State α × Option α :=
  (⟨true, none⟩, state.waiter)

def State.unregister (state : State α) : State α := { state with waiter := none }

/-- Subscribe once to a producer task. Repeated heartbeat selections replace and
remove one waiter instead of accumulating one task callback per heartbeat. -/
def ofTask (task : Task α) : IO (Selector Unit) := do
  let state ← Std.Mutex.new ({} : State (Waiter Unit))
  let deliver := fun (waiter : Waiter Unit) =>
    waiter.race (pure ()) (fun promise => promise.resolve (.ok ()))
  BaseIO.chainTask task fun _ => do
    let notify ← state.atomically do
      let (next, notify) := (← get).finish
      set next
      return notify
    if let some waiter := notify then deliver waiter
  return {
    tryFn := do return if (← state.atomically get).ready then some () else none
    registerFn := fun waiter => do
      let notify ← state.atomically do
        let (next, notify) := (← get).register waiter
        set next
        return notify
      if let some waiter := notify then deliver waiter
    unregisterFn := state.atomically do modify State.unregister }

end FastHTTP.ReadySignal
