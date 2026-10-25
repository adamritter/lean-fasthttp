import FastHTTP.ReadySignal

namespace FastHTTP.ReadySignal

/-- Completion followed by registration immediately notifies the new waiter. -/
theorem finish_before_register (s : State α) (w : α) :
    ((s.finish).1.register w).2 = some w := by
  simp [State.finish, State.register]

/-- Registration followed by completion cannot lose the registered waiter. -/
theorem register_before_finish (s : State α) (w : α) (h : s.ready = false) :
    ((s.register w).1.finish).2 = some w := by
  simp [State.register, State.finish, h]

/-- Both mutex orderings deliver; this concerns state transitions, not scheduler fairness. -/
theorem registration_delivery (s : State α) (w : α) :
    (s.register w).2 = some w ∨ ((s.register w).1.finish).2 = some w := by
  cases h : s.ready <;> simp [State.register, State.finish, h]

theorem finish_is_ready (s : State α) : s.finish.1.ready = true := rfl

theorem finish_releases_waiter (s : State α) : s.finish.1.waiter = none := rfl

theorem repeated_finish_no_notification (s : State α) : s.finish.1.finish.2 = none := rfl

theorem unregister_preserves_ready (s : State α) : s.unregister.ready = s.ready := rfl

theorem unregister_releases_waiter (s : State α) : s.unregister.waiter = none := rfl

/-- A heartbeat winning selection does not consume a concurrent completion. -/
theorem finish_unregister_register (s : State α) (w : α) :
    (s.finish.1.unregister.register w).2 = some w := by
  simp [State.finish, State.unregister, State.register]

theorem unregister_finish_register (s : State α) (w : α) :
    (s.unregister.finish.1.register w).2 = some w := by
  simp [State.finish, State.unregister, State.register]

end FastHTTP.ReadySignal
