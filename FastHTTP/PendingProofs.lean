import FastHTTP.Pending

namespace FastHTTP

/-- These are the transitions executed under Pending's mutex. Taking or closing
a gate consumes its stored value; repeated operations cannot dispose it again. -/
theorem pending_close_idempotent (state : PendingState α) :
    (state.close.1).close = (.closed, none, false) := by
  cases state <;> rfl

theorem pending_take_once (state : PendingState α) :
    ((state.take.1).take).2 = none := by
  cases state <;> rfl

theorem pending_late_result (value : α) :
    (PendingState.closed : PendingState α).resolve value = (.closed, some value) := rfl

theorem pending_cancel_before_resolve (value : α) :
    ((PendingState.waiting : PendingState α).close.1).resolve value = (.closed, some value) := rfl

theorem pending_resolve_before_cancel (value : α) :
    ((PendingState.waiting : PendingState α).resolve value).1.close = (.closed, some value, true) := rfl

theorem pending_taken_not_cancelled (value : α) :
    ((PendingState.resolved value).take.1).close = (.closed, none, false) := rfl

end FastHTTP
