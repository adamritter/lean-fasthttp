import FastHTTP.Action

namespace FastHTTP.Action

theorem pure_ready (value : α) :
    (pure value : Action α).run = pure (.ready value) := rfl

theorem io_ready (action : IO α) :
    (ofIO action).run = (do return .ready (← action)) := rfl

theorem context_scoped (action : Std.Async.ContextAsync α) :
    (ofContext action).run = pure (.scoped action) := rfl

/-- Once scoped, bind passes the identical context to the entire continuation. -/
theorem scoped_bind (action : Std.Async.ContextAsync α) (next : α → Action β) :
    bindStep (.scoped action) next = pure (.scoped fun context => do
      let value ← action context
      (next value).inContext context) := rfl

theorem ready_bind (value : α) (next : α → Action β) :
    bindStep (.ready value) next = (next value).run := rfl

end FastHTTP.Action
