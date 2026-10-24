import FastHTTP.DriverOutputProofs
import LeanUV.ProgressContract

namespace FastHTTP.Protocol

set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

/-- Work on one dispatched request; receiving incomplete input is outside this
phase. An application may stream indefinitely, so its finite-body premise below
is deliberately separate from protocol safety. -/
def ActiveReply : Driver.State → Prop
  | .reading _ | .continuing _ | .closed => False
  | .streaming stream => stream.control.phase ≠ .done
  | _ => True

def EndContinuation : Driver.State → Bool
  | .streaming stream => decide (stream.control.phase = .endWrite)
  | _ => false

/-- A final response was acknowledged, or this request's stream/transport was
interrupted. Cleanup following EOF is NOT completion: its terminal chunk still
has to be written and acknowledged. -/
def ReplyExit (cfg : Config) (state : Driver.State) (event : Driver.Event) : Prop :=
  (Driver.step cfg state event).1 = .closed ∨
  match state, event with
  | _, .failed | _, .closed => True
  | .sending _, .written => True
  | .streaming stream, .written => stream.control.phase = .endWrite ∨
      (stream.control.phase = .headers ∧ stream.request.isHead = true)
  | .streaming _, .result .failed => True
  | .streaming stream, .result (.chunk none) => stream.request.versionMinor = 0
  | .streaming _, .result (.chunk (some bytes)) => bytes.isEmpty = true
  | .releasing next _, .result .released => ¬EndContinuation next
  | _, _ => False

/-- Four units per remaining producer chunk pay for producer invocation, promise
completion and write acknowledgment; fixed administrative phases strictly descend. -/
def ReplyRank (budget : Nat) (state : Driver.State) (command : Driver.Command) : Nat :=
  match state with
  | .handling _ _ => 4 * budget + (match command with | .perform (.response _) => 7 | _ => 8)
  | .preparing _ _ => 2
  | .sending _ => 1
  | .streamDate _ => 4 * budget + 6
  | .streaming stream => match stream.control.phase with
    | .headers | .chunkWrite => 4 * budget + 5
    | .producer => 4 * budget + (match command with | .perform (.chunk _) => 3 | _ => 4)
    | .endWrite => 1
    | .done => 0
  | .releasing next _ => if EndContinuation next then 2 else 0
  | _ => 0

theorem active_reply_busy (state : Driver.State) (command : Driver.Command)
    (valid : OutputPair state command) (active : ActiveReply state) : LeanUV.TCP.Machine.Busy command := by
  cases state with
  | reading _ | continuing _ | closed => contradiction
  | handling request rest => rcases valid with rfl | ⟨promise, rfl⟩ <;> trivial
  | preparing purpose response => subst command; trivial
  | sending purpose => obtain ⟨buffers, rfl, _⟩ := valid; trivial
  | streamDate stream => rw [valid.1]; trivial
  | streaming stream =>
    cases phase : stream.control.phase <;> simp_all [StreamOutput, ActiveReply, OutputPair]
    · obtain ⟨buffers, rfl, _⟩ := valid; trivial
    · rcases valid.2 with rfl | ⟨promise, rfl⟩ <;> trivial
    · obtain ⟨_, payload, _, rfl, _⟩ := valid; trivial
    · obtain ⟨_, _, rfl⟩ := valid; trivial
  | releasing next pending => obtain ⟨⟨action, rfl⟩, _⟩ := valid; trivial

theorem reject_reply_rank (status budget : Nat) (notClosed : (Driver.reject status).1 ≠ .closed) :
    ActiveReply (Driver.reject status).1 ∧ ReplyRank budget (Driver.reject status).1 (Driver.reject status).2 = 2 := by
  unfold Driver.reject at *
  repeat' first | split | dsimp only
  all_goals simp_all [ActiveReply, ReplyRank]

/-- All input assumptions here concern job/result scheduling and a finite bound
on application chunks. The decreasing HTTP phase rank is proved, not assumed. -/
theorem driver_reply_descent (cfg : Config) (state : Driver.State) (prior : Driver.Command) (event : Driver.Event)
    (before after : Nat) (valid : OutputPair state prior) (active : ActiveReply state)
    (allowed : LeanUV.TCP.Machine.permitted prior event)
    (effect : LeanUV.TCP.Machine.effectMatches Driver.EffectShape prior event)
    (unfinished : ¬ReplyExit cfg state event) (budget : after ≤ before)
    (spent : ∀ bytes, event = .result (.chunk (some bytes)) → after < before) :
    ActiveReply (Driver.step cfg state event).1 ∧
      ReplyRank after (Driver.step cfg state event).1 (Driver.step cfg state event).2 < ReplyRank before state prior := by
  cases event with
  | closed => exact False.elim (unfinished (Or.inr trivial))
  | failed => exact False.elim (unfinished (Or.inr trivial))
  | data bytes =>
    have busy := active_reply_busy state prior valid active
    cases prior <;> simp_all [LeanUV.TCP.Machine.Busy, LeanUV.TCP.Machine.permitted]
  | written =>
    cases state with
    | reading _ | continuing _ | closed => contradiction
    | handling request rest => rcases valid with rfl | ⟨promise, rfl⟩ <;> contradiction
    | preparing purpose response => subst prior; contradiction
    | sending purpose => exact False.elim (unfinished (Or.inr trivial))
    | streamDate stream => rw [valid.1] at allowed; contradiction
    | releasing next pending => obtain ⟨⟨action, rfl⟩, _⟩ := valid; contradiction
    | streaming stream =>
      have enabled := output_stream_written_enabled stream prior valid allowed
      have notExit := (not_or.mp unfinished).2
      rcases enabled with phase | phase | phase
      · have notHead : stream.request.isHead = false := by simpa [phase] using notExit
        simp [Driver.step, Driver.streamEvent, streamStep, phase, notHead, Driver.streamCommand, ActiveReply, ReplyRank]
        omega
      · simp [Driver.step, Driver.streamEvent, streamStep, phase, Driver.streamCommand, ActiveReply, ReplyRank]
        omega
      · exact False.elim (notExit (Or.inl phase))
  | result result =>
    cases state with
    | reading _ | continuing _ | closed => contradiction
    | handling request rest =>
      rcases valid with rfl | ⟨promise, rfl⟩
      · cases result <;> simp only [LeanUV.TCP.Machine.effectMatches, Driver.EffectShape] at effect
        all_goals try contradiction
        case handled reply =>
          cases reply <;> simp [Driver.step, ActiveReply, ReplyRank] <;> omega
        case failed =>
          have notClosed : (Driver.reject 500).1 ≠ .closed := (not_or.mp unfinished).1
          have next := reject_reply_rank 500 after notClosed
          refine ⟨next.1, ?_⟩
          change ReplyRank after (Driver.reject 500).1 (Driver.reject 500).2 < 4 * before + 8
          rw [next.2]
          omega
      · cases result <;> simp only [LeanUV.TCP.Machine.effectMatches, Driver.EffectShape] at effect
        all_goals try contradiction
        case response response => simp [Driver.step, ActiveReply, ReplyRank] <;> omega
        case failed =>
          have notClosed : (Driver.reject 500).1 ≠ .closed := (not_or.mp unfinished).1
          have next := reject_reply_rank 500 after notClosed
          refine ⟨next.1, ?_⟩
          change ReplyRank after (Driver.reject 500).1 (Driver.reject 500).2 < 4 * before + 7
          rw [next.2]
          omega
    | preparing purpose response =>
      change prior = .perform .date at valid
      subst prior
      cases result <;> simp_all [LeanUV.TCP.Machine.effectMatches, Driver.EffectShape, Driver.step, ActiveReply, ReplyRank]
    | sending purpose => obtain ⟨buffers, rfl, _⟩ := valid; contradiction
    | streamDate stream =>
      obtain ⟨rfl, phase⟩ := valid
      cases result <;> simp_all [LeanUV.TCP.Machine.effectMatches, Driver.EffectShape, Driver.step, ActiveReply, ReplyRank]
      omega
    | releasing next pending =>
      obtain ⟨⟨action, rfl⟩, nextValid⟩ := valid
      cases result <;> simp only [LeanUV.TCP.Machine.effectMatches, Driver.EffectShape] at effect
      all_goals try contradiction
      have ending : EndContinuation next = true := by
        simpa using (not_or.mp unfinished).2
      cases next <;> simp_all [EndContinuation, Driver.step, ActiveReply, ReplyRank]
    | streaming stream =>
      have phase := output_stream_result_enabled stream prior result valid allowed
      simp only [OutputPair, StreamOutput, phase] at valid
      rcases valid.2 with rfl | ⟨promise, rfl⟩
      · cases result <;> simp only [LeanUV.TCP.Machine.effectMatches, Driver.EffectShape] at effect
        all_goals try contradiction
        case producer promise => simp [Driver.step, ActiveReply, ReplyRank, phase]; omega
        case failed => exact False.elim (unfinished (Or.inr trivial))
      · cases result <;> simp only [LeanUV.TCP.Machine.effectMatches, Driver.EffectShape] at effect
        all_goals try contradiction
        case failed => exact False.elim (unfinished (Or.inr trivial))
        case chunk bytes =>
          cases bytes with
          | none =>
            have modern : stream.request.versionMinor ≠ 0 := (not_or.mp unfinished).2
            cases owns : stream.control.ownsResource <;>
              simp [Driver.step, Driver.streamEvent, streamStep, phase, modern, owns,
                Driver.streamCommand, ActiveReply, ReplyRank, EndContinuation] <;> omega
          | some bytes =>
            have nonempty : bytes.isEmpty = false := by simpa using (not_or.mp unfinished).2
            have decrease := spent bytes rfl
            simp [Driver.step, Driver.streamEvent, streamStep, phase, nonempty,
              Driver.streamCommand, ActiveReply, ReplyRank]
            omega


/-- A finite producer supplies a natural bound on remaining nonempty chunks.
This is an APPLICATION termination premise. Budget can reset after a response
finishes/aborts; it cannot grow during one response. Infinite SSE intentionally
does not satisfy it, while all safety theorems remain applicable to SSE. -/
structure FiniteProducerBudget (cfg : Config) (states : Nat → Driver.State)
    (commands : Nat → Driver.Command) (budget : Nat → Nat) : Prop where
  remaining : ∀ first next event,
    LeanUV.TCP.Machine.Dispatch (Driver.machine cfg) Driver.EffectShape states commands first next event →
    ¬ReplyExit cfg (states first) event →
      budget next ≤ budget first ∧
      (∀ bytes, event = .result (.chunk (some bytes)) → budget next < budget first)

/-- Conditional liveness for the real controller: from any dispatched request,
a finite producer and responsive external operations eventually lead to a final
write acknowledgment or an explicit interruption. Every observation's HTTP
invariant is DERIVED from generic execution refinement, not assumed as progress.
There is no fixed response-time bound and no claim that a remote app consumed it. -/
theorem driver_eventual_reply (cfg : Config) (states : Nat → Driver.State)
    (commands : Nat → Driver.Command) (budget : Nat → Nat)
    (observed : ∀ n, ∃ events decisions,
      LeanUV.TCP.Machine.ExecutionContract (Driver.machine cfg) events (states n) decisions Driver.EffectShape ∧
      commands n = decisions.getLastD .idle)
    (responsive : LeanUV.TCP.Machine.ResponsiveContract (Driver.machine cfg) Driver.EffectShape states commands)
    (finite : FiniteProducerBudget cfg states commands budget)
    (first : Nat) (active : ActiveReply (states first)) :
    ∃ checkpoint next event, first ≤ checkpoint ∧
      LeanUV.TCP.Machine.Dispatch (Driver.machine cfg) Driver.EffectShape states commands checkpoint next event ∧
      ReplyExit cfg (states checkpoint) event := by
  have valid : ∀ n, OutputPair (states n) (commands n) := by
    intro n
    obtain ⟨events, decisions, execution, command⟩ := observed n
    rw [command]
    exact LeanUV.TCP.Machine.execution_scheduled_invariant (Driver.machine cfg) Driver.EffectShape OutputPair
      rfl (driver_step_output cfg) events (states n) decisions execution
  apply LeanUV.TCP.Machine.responsive_descent (Driver.machine cfg) Driver.EffectShape states commands responsive
    (fun n => ActiveReply (states n)) (fun n => ReplyRank (budget n) (states n) (commands n)) (ReplyExit cfg)
    (fun n h => active_reply_busy _ _ (valid n) h) ?_ first active
  intro n next event current dispatch unfinished
  have supply := finite.remaining n next event dispatch unfinished
  have progress := driver_reply_descent cfg (states n) (commands n) event (budget n) (budget next)
    (valid n) current dispatch.enabled dispatch.matching unfinished supply.1 supply.2
  have stateEq := dispatch.state
  have commandEq := dispatch.command
  change states next = (Driver.step cfg (states n) event).1 at stateEq
  change commands next = (Driver.step cfg (states n) event).2 at commandEq
  simpa only [←stateEq, ←commandEq] using progress

end FastHTTP.Protocol
