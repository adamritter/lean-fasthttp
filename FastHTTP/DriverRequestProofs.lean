import FastHTTP.DriverProofs

namespace FastHTTP.Protocol

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

/-- A delivered request is the exact first message of some accumulated input,
including its pipeline remainder. The witness is raw wire data, not an oracle. -/
def DeliveredRequest (cfg : Config) (request : Request) (rest : ByteArray) : Prop :=
  ∃ wire, RequestWire cfg wire request rest

def DriverPurposeValid (cfg : Config) : Driver.Purpose → Prop
  | .response request rest => DeliveredRequest cfg request rest
  | .rejection => True

def DriverCommandValid (cfg : Config) : Driver.Command → Prop
  | .perform (.handle request) => ∃ rest, DeliveredRequest cfg request rest
  | _ => True

/-- A ghost wire witness follows the same complete request through reading,
Expect, handler promises, prepared/streaming responses, cleanup and pipelining.
It is erased from the runtime and never influences routing or acceptance. -/
def DriverRequestInvariant (cfg : Config) : Driver.State → Prop
  | .reading parser => StateBound parser ∧ ∃ wire,
      acknowledge cfg (feed cfg .head wire) = .need parser
  | .continuing parser => StateBound parser ∧ ∃ wire,
      acknowledge cfg (feed cfg parser .empty) = acknowledge cfg (feed cfg .head wire)
  | .handling request rest => DeliveredRequest cfg request rest
  | .preparing purpose _ | .sending purpose => DriverPurposeValid cfg purpose
  | .streamDate stream | .streaming stream => DeliveredRequest cfg stream.request stream.rest
  | .releasing next command => DriverRequestInvariant cfg next ∧ DriverCommandValid cfg command
  | .closed => True

def DriverPairValid (cfg : Config) (pair : Driver.State × Driver.Command) : Prop :=
  DriverRequestInvariant cfg pair.1 ∧ DriverCommandValid cfg pair.2

theorem driver_initial_request_invariant (cfg : Config) : DriverRequestInvariant cfg .reading :=
  ⟨initial_state_bound, .empty, by rw [feed_empty_need]; rfl⟩

theorem driver_reject_valid (cfg : Config) (status : Nat) : DriverPairValid cfg (Driver.reject status) := by
  unfold DriverPairValid Driver.reject
  repeat' first | split | dsimp only
  all_goals simp [DriverRequestInvariant, DriverPurposeValid, DriverCommandValid]

theorem driver_accept_valid (cfg : Config) (step : Step) (wire : ByteArray)
    (bound : StepBound step)
    (same : acknowledge cfg step = acknowledge cfg (feed cfg .head wire)) :
    DriverPairValid cfg (Driver.accept step) := by
  cases step with
  | need parser => exact ⟨⟨bound, wire, same.symm⟩, trivial⟩
  | «continue» parser =>
    have twice := congrArg (acknowledge cfg) same
    rw [acknowledge_initial_idempotent] at twice
    exact ⟨⟨bound, wire, twice⟩, trivial⟩
  | request request rest =>
    have grammar := (feed_request_grammar_iff cfg wire request rest).mp same.symm
    exact ⟨⟨wire, grammar⟩, rest, wire, grammar⟩
  | reject status => exact driver_reject_valid cfg status

theorem driver_resume_valid (cfg : Config) (purpose : Driver.Purpose) : DriverPairValid cfg (Driver.resume cfg purpose) := by
  cases purpose with
  | rejection => exact ⟨trivial, trivial⟩
  | response request rest =>
    simp only [Driver.resume]
    split
    · exact ⟨trivial, trivial⟩
    · split
      · exact ⟨driver_initial_request_invariant cfg, trivial⟩
      · exact driver_accept_valid cfg (feed cfg .head rest) rest (feed_bound cfg .head rest initial_state_bound) rfl

theorem driver_streamCommand_valid (cfg : Config) (stream : Driver.Streaming) (command : StreamCommand)
    (valid : DeliveredRequest cfg stream.request stream.rest) :
    DriverPairValid cfg (Driver.streamCommand cfg stream command) := by
  cases command <;> simp only [Driver.streamCommand]
  all_goals first
    | exact ⟨valid, trivial⟩
    | exact driver_resume_valid cfg _
    | exact ⟨trivial, trivial⟩

theorem driver_streamEvent_valid (cfg : Config) (stream : Driver.Streaming) (event : StreamEvent)
    (valid : DeliveredRequest cfg stream.request stream.rest) : DriverPairValid cfg (Driver.streamEvent cfg stream event) := by
  have next := driver_streamCommand_valid cfg
    { stream with control := (streamStep stream.request stream.control event).state }
    (streamStep stream.request stream.control event).command valid
  unfold Driver.streamEvent
  dsimp only
  split
  · exact ⟨next, trivial⟩
  · exact next

theorem driver_stop_valid (cfg : Config) (state : Driver.State) (command : Driver.Command)
    (valid : DriverCommandValid cfg command) : DriverPairValid cfg (Driver.stop state command) := by
  cases state <;> simp [Driver.stop, DriverPairValid, DriverRequestInvariant, DriverCommandValid, valid]
  all_goals split <;> simp_all [DriverRequestInvariant, DriverCommandValid]

/-- Every handler invocation made by the actual connection controller receives a
complete grammatical request. The invariant follows arbitrary receive fragments,
acknowledgments, application replies, producer results, closure and pipelines. -/
theorem driver_step_request_valid (cfg : Config) (state : Driver.State) (event : Driver.Event)
    (valid : DriverRequestInvariant cfg state) : DriverPairValid cfg (Driver.step cfg state event) := by
  cases event with
  | closed => exact driver_stop_valid cfg state .idle trivial
  | failed => exact driver_stop_valid cfg state .abort trivial
  | data bytes =>
    cases state <;> simp only [Driver.step]
    · rename_i parser
      obtain ⟨bound, wire, prior⟩ := valid
      have same := feed_acknowledged_fragmentation cfg wire bytes
      rw [prior] at same
      exact driver_accept_valid cfg (feed cfg parser bytes) (wire ++ bytes) (feed_bound cfg parser bytes bound) same.symm
    all_goals first | exact driver_stop_valid cfg _ .abort trivial | exact ⟨trivial, trivial⟩
  | written =>
    cases state <;> simp only [Driver.step]
    · exact driver_stop_valid cfg _ .abort trivial
    · obtain ⟨bound, wire, same⟩ := valid
      exact driver_accept_valid cfg _ wire (feed_bound cfg _ .empty bound) same
    · exact driver_stop_valid cfg _ .abort trivial
    · exact driver_stop_valid cfg _ .abort trivial
    · exact driver_resume_valid cfg _
    · exact driver_stop_valid cfg _ .abort trivial
    · exact driver_streamEvent_valid cfg _ .written valid
    · exact driver_stop_valid cfg _ .abort trivial
    · exact ⟨trivial, trivial⟩
  | result result =>
    cases state <;> cases result <;> simp only [Driver.step]
    all_goals try first
      | exact driver_stop_valid cfg _ .abort trivial
      | exact driver_streamEvent_valid cfg _ _ valid
      | exact driver_reject_valid cfg 500
      | exact valid
      | (constructor; exact valid; trivial)
      | (constructor <;> trivial)
    case handling.handled request rest reply =>
      cases reply <;> exact ⟨valid, trivial⟩
    case streaming.chunk stream bytes =>
      cases bytes <;> exact driver_streamEvent_valid cfg stream _ valid

/-- Every command in the actual pure replay satisfies the handler-dispatch
predicate, not only its final state or final command. -/
theorem driver_replay_requests_valid (cfg : Config) (state : Driver.State) (events : List Driver.Event)
    (valid : DriverRequestInvariant cfg state) :
    DriverRequestInvariant cfg ((Driver.machine cfg).replay state events).1 ∧
      ∀ command ∈ ((Driver.machine cfg).replay state events).2, DriverCommandValid cfg command := by
  induction events generalizing state with
  | nil => exact ⟨valid, by simp [LeanUV.TCP.Machine.replay]⟩
  | cons event events ih =>
    have step := driver_step_request_valid cfg state event valid
    have tail := ih (Driver.step cfg state event).1 step.1
    refine ⟨tail.1, ?_⟩
    intro command member
    simp only [LeanUV.TCP.Machine.replay, Driver.machine, List.mem_cons] at member
    rcases member with rfl | member
    · exact step.2
    · exact tail.2 command member

/-- End-to-end dispatch safety for FastHTTP.UV under the explicit generic adapter
execution contract. No grammar fact is assumed from libuv or the application. -/
theorem driver_native_requests_valid (cfg : Config) (events : List Driver.Event)
    (final : Driver.State) (commands : List Driver.Command)
    (execution : LeanUV.TCP.Machine.ExecutionContract (Driver.machine cfg) events final commands Driver.EffectShape) :
    ∀ request, .perform (.handle request) ∈ commands → ∃ rest wire, RequestWire cfg wire request rest := by
  have h := driver_replay_requests_valid cfg (Driver.machine cfg).initial events (driver_initial_request_invariant cfg)
  rw [execution.refinement] at h
  intro request member
  exact h.2 (.perform (.handle request)) member

end FastHTTP.Protocol
