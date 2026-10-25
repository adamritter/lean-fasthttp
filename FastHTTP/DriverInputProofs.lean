import FastHTTP.DriverRequestProofs
import LeanUV.AdapterContract

namespace FastHTTP.Protocol

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

/-- The pipeline remainder is an exact proper suffix of the actual first-message
wire. At least the sixteen-octet minimal request head has been consumed. -/
theorem request_wire_suffix (cfg : Config) (wire : ByteArray) (request : Request) (rest : ByteArray)
    (valid : RequestWire cfg wire request rest) :
    ∃ consumed : ByteArray, 16 ≤ consumed.size ∧ wire = consumed ++ rest := by
  obtain ⟨_, headEnd, _, head, headGrammar, bodyGrammar⟩ := valid
  have headMin := headGrammar.1.2.1
  have headBound := headGrammar.1.1
  simp only [ByteArray.size_extract, Nat.sub_zero] at headBound
  have hb : headEnd ≤ wire.size := by omega
  have finish : ∃ stop, 16 ≤ stop ∧ stop ≤ wire.size ∧ rest = wire.extract stop wire.size := by
    unfold HeadBodyGrammar at bodyGrammar
    split at bodyGrammar
    · exact ⟨headEnd, headMin, hb, bodyGrammar.2⟩
    · obtain ⟨body, trailers, stop, ⟨consumed, suffix, partition, _, endEq⟩, _, restEq⟩ := bodyGrammar
      have lengths := congrArg List.length partition
      simp only [List.length_drop, Array.length_toList, List.length_append] at lengths
      change headEnd ≤ wire.data.size at hb
      refine ⟨stop, by omega, ?_, restEq⟩
      change stop ≤ wire.data.size
      omega
  obtain ⟨stop, positive, bound, rfl⟩ := finish
  refine ⟨wire.extract 0 stop, ?_, ?_⟩
  · simp [ByteArray.size_extract, Nat.min_eq_left bound, positive]
  · rw [ByteArray.extract_append_extract]
    simp [Nat.max_eq_right bound]

/-- Independent input-ledger operations: receive unchanged octets, or consume
exactly one grammatical first message. No parser/driver implementation occurs in
this relation, and consuming cannot move backward or invent bytes. -/
inductive InputShift (cfg : Config) : ByteArray → ByteArray → Prop where
  | stay (wire : ByteArray) : InputShift cfg wire wire
  | consume (wire : ByteArray) (request : Request) (rest : ByteArray) :
      RequestWire cfg wire request rest → InputShift cfg wire rest

def eventInput (wire : ByteArray) : Driver.Event → ByteArray
  | .data bytes => wire ++ bytes
  | _ => wire

def eventOctets : Driver.Event → List UInt8
  | .data bytes => bytes.data.toList
  | _ => []

def InputPurpose (cfg : Config) (wire : ByteArray) : Driver.Purpose → Prop
  | .response request rest => RequestWire cfg wire request rest
  | .rejection => True

def InputCommand (cfg : Config) (wire : ByteArray) : Driver.Command → Prop
  | .perform (.handle request) => ∃ rest, RequestWire cfg wire request rest
  | _ => True

/-- The wire witness is now indexed by the actual receive/consume ledger. -/
def InputState (cfg : Config) (wire : ByteArray) : Driver.State → Prop
  | .reading parser => StateBound parser ∧ acknowledge cfg (feed cfg .head wire) = .need parser
  | .continuing parser => StateBound parser ∧
      acknowledge cfg (feed cfg parser .empty) = acknowledge cfg (feed cfg .head wire)
  | .handling request rest | .waiting request rest _ => RequestWire cfg wire request rest
  | .preparing purpose _ | .sending purpose => InputPurpose cfg wire purpose
  | .streamDate stream | .streaming stream => RequestWire cfg wire stream.request stream.rest
  | .releasing next command => InputState cfg wire next ∧ InputCommand cfg wire command
  | .closed => True

def InputPair (cfg : Config) (wire : ByteArray) (pair : Driver.State × Driver.Command) : Prop :=
  InputState cfg wire pair.1 ∧ InputCommand cfg wire pair.2

theorem input_initial (cfg : Config) : InputState cfg .empty .reading :=
  ⟨initial_state_bound, by rw [feed_empty_need]; rfl⟩

theorem input_reject (cfg : Config) (wire : ByteArray) (status : Nat) : InputPair cfg wire (Driver.reject status) := by
  unfold InputPair Driver.reject
  repeat' first | split | dsimp only
  all_goals simp [InputState, InputPurpose, InputCommand]

theorem input_accept (cfg : Config) (wire : ByteArray) (step : Step) (bound : StepBound step)
    (same : acknowledge cfg step = acknowledge cfg (feed cfg .head wire)) :
    InputPair cfg wire (Driver.accept step) := by
  cases step with
  | need parser => exact ⟨⟨bound, same.symm⟩, trivial⟩
  | «continue» parser =>
    have twice := congrArg (acknowledge cfg) same
    rw [acknowledge_initial_idempotent] at twice
    exact ⟨⟨bound, twice⟩, trivial⟩
  | request request rest =>
    have grammar := (feed_request_grammar_iff cfg wire request rest).mp same.symm
    exact ⟨grammar, rest, grammar⟩
  | reject status => exact input_reject cfg wire status

theorem input_resume (cfg : Config) (wire : ByteArray) (purpose : Driver.Purpose)
    (valid : InputPurpose cfg wire purpose) :
    ∃ nextWire, InputShift cfg wire nextWire ∧ InputPair cfg nextWire (Driver.resume cfg purpose) := by
  cases purpose with
  | rejection => exact ⟨wire, .stay wire, trivial, trivial⟩
  | response request rest =>
    refine ⟨rest, .consume wire request rest valid, ?_⟩
    simp only [Driver.resume]
    split
    · exact ⟨trivial, trivial⟩
    · split
      · rename_i close empty
        have h : rest = .empty := by simpa [ByteArray.isEmpty] using empty
        subst rest
        exact ⟨input_initial cfg, trivial⟩
      · exact input_accept cfg rest (feed cfg .head rest) (feed_bound cfg .head rest initial_state_bound) rfl

theorem input_stream_command (cfg : Config) (wire : ByteArray) (stream : Driver.Streaming) (command : StreamCommand)
    (valid : RequestWire cfg wire stream.request stream.rest) :
    ∃ nextWire, InputShift cfg wire nextWire ∧ InputPair cfg nextWire (Driver.streamCommand cfg stream command) := by
  cases command <;> simp only [Driver.streamCommand]
  all_goals first
    | exact ⟨wire, .stay wire, valid, trivial⟩
    | exact input_resume cfg wire _ valid
    | exact ⟨wire, .stay wire, trivial, trivial⟩

theorem input_stream_event (cfg : Config) (wire : ByteArray) (stream : Driver.Streaming) (event : StreamEvent)
    (valid : RequestWire cfg wire stream.request stream.rest) :
    ∃ nextWire, InputShift cfg wire nextWire ∧ InputPair cfg nextWire (Driver.streamEvent cfg stream event) := by
  obtain ⟨nextWire, shift, next⟩ := input_stream_command cfg wire
    { stream with control := (streamStep stream.request stream.control event).state }
    (streamStep stream.request stream.control event).command valid
  refine ⟨nextWire, shift, ?_⟩
  unfold Driver.streamEvent
  dsimp only
  split
  · exact ⟨next, trivial⟩
  · exact next

theorem input_stop (cfg : Config) (wire : ByteArray) (state : Driver.State) (command : Driver.Command)
    (valid : InputCommand cfg wire command) : InputPair cfg wire (Driver.stop state command) := by
  cases state <;> simp [Driver.stop, InputPair, InputState, InputCommand, valid]
  all_goals split <;> simp_all [InputState, InputCommand]

/-- Actual controller refinement of the independent receive/consume ledger. A
handler command is certified against the current ledger window, never arbitrary
existential bytes unrelated to the connection. -/
theorem driver_step_input (cfg : Config) (wire : ByteArray) (state : Driver.State) (event : Driver.Event)
    (valid : InputState cfg wire state) :
    ∃ nextWire, InputShift cfg (eventInput wire event) nextWire ∧
      InputPair cfg nextWire (Driver.step cfg state event) := by
  cases event with
  | closed => exact ⟨wire, .stay wire, input_stop cfg wire state .idle trivial⟩
  | failed => exact ⟨wire, .stay wire, input_stop cfg wire state .abort trivial⟩
  | data bytes =>
    cases state <;> simp only [Driver.step, eventInput]
    · rename_i parser
      obtain ⟨bound, prior⟩ := valid
      have same := feed_acknowledged_fragmentation cfg wire bytes
      rw [prior] at same
      exact ⟨wire ++ bytes, .stay _, input_accept cfg (wire ++ bytes) (feed cfg parser bytes)
        (feed_bound cfg parser bytes bound) same.symm⟩
    all_goals first
      | exact ⟨wire ++ bytes, .stay _, input_stop cfg _ _ .abort trivial⟩
      | exact ⟨wire ++ bytes, .stay _, trivial, trivial⟩
  | written =>
    cases state <;> simp only [Driver.step, eventInput]
    · exact ⟨wire, .stay _, input_stop cfg _ _ .abort trivial⟩
    · exact ⟨wire, .stay _, input_accept cfg wire _ (feed_bound cfg _ .empty valid.1) valid.2⟩
    · exact ⟨wire, .stay _, input_stop cfg _ _ .abort trivial⟩
    · exact ⟨wire, .stay _, input_stop cfg _ _ .abort trivial⟩
    · exact input_resume cfg wire _ valid
    · exact ⟨wire, .stay _, input_stop cfg _ _ .abort trivial⟩
    · exact input_stream_event cfg wire _ .written valid
    · exact ⟨wire, .stay _, input_stop cfg _ _ .abort trivial⟩
    · exact ⟨wire, .stay _, input_stop cfg _ _ .abort trivial⟩
    · exact ⟨wire, .stay _, trivial, trivial⟩
  | result result =>
    cases state <;> cases result <;> simp only [Driver.step, eventInput]
    all_goals try first
      | exact ⟨wire, .stay _, input_stop cfg _ _ .abort trivial⟩
      | exact input_stream_event cfg wire _ _ valid
      | exact ⟨wire, .stay _, input_reject cfg wire 500⟩
      | exact ⟨wire, .stay _, valid⟩
      | (refine ⟨wire, .stay _, ?_⟩; constructor; exact valid; trivial)
      | (refine ⟨wire, .stay _, ?_⟩; constructor <;> trivial)
    case handling.handled request rest reply =>
      cases reply <;> exact ⟨wire, .stay _, valid, trivial⟩
    case streaming.chunk stream bytes =>
      cases bytes <;> exact input_stream_event cfg wire stream _ valid
    case waiting.completed request rest pending completion =>
      cases completion <;> exact ⟨wire, .stay _, valid, trivial⟩
    case waiting.failed request rest pending =>
      exact ⟨wire, .stay _, input_reject cfg wire 500, trivial⟩

/-- A protocol specification over observations and commands, independent of the
controller implementation. Successive windows only grow by observed reads or
advance by one complete RequestWire production. -/
inductive InputTrace (cfg : Config) : ByteArray → List Driver.Event → List Driver.Command → ByteArray → Prop where
  | nil (wire : ByteArray) : InputTrace cfg wire [] [] wire
  | next (wire after final : ByteArray) (event : Driver.Event) (command : Driver.Command)
      (events : List Driver.Event) (commands : List Driver.Command) :
      InputShift cfg (eventInput wire event) after → InputCommand cfg after command →
      InputTrace cfg after events commands final → InputTrace cfg wire (event :: events) (command :: commands) final

theorem driver_replay_input (cfg : Config) (wire : ByteArray) (state : Driver.State) (events : List Driver.Event)
    (valid : InputState cfg wire state) :
    ∃ finalWire, InputState cfg finalWire ((Driver.machine cfg).replay state events).1 ∧
      InputTrace cfg wire events ((Driver.machine cfg).replay state events).2 finalWire := by
  induction events generalizing wire state with
  | nil => exact ⟨wire, valid, .nil wire⟩
  | cons event events ih =>
    obtain ⟨nextWire, shift, nextState, command⟩ := driver_step_input cfg wire state event valid
    obtain ⟨finalWire, finalState, trace⟩ := ih nextWire (Driver.step cfg state event).1 nextState
    exact ⟨finalWire, finalState, .next wire nextWire finalWire event _ events _ shift command trace⟩

/-- Every consumption removes at least a minimal head; the exact suffix remains. -/
theorem input_shift_partition (cfg : Config) (wire after : ByteArray) (shift : InputShift cfg wire after) :
    ∃ consumed : ByteArray, wire = consumed ++ after ∧ (consumed = .empty ∨ 16 ≤ consumed.size) := by
  cases shift with
  | stay => exact ⟨.empty, by simp, Or.inl rfl⟩
  | consume =>
    obtain ⟨consumed, bound, partition⟩ := request_wire_suffix cfg wire _ after (by assumption)
    exact ⟨consumed, partition, Or.inr bound⟩


/-- Current unconsumed window is an exact suffix of the observed octets. -/
def InputWindow (received : List UInt8) (wire : ByteArray) : Prop :=
  ∃ consumed, received = consumed ++ wire.data.toList

def InputSegment (cfg : Config) (received : List UInt8) (request : Request) : Prop :=
  ∃ before wire after rest, received = before ++ wire.data.toList ++ after ∧ RequestWire cfg wire request rest

theorem input_event_window (received : List UInt8) (wire : ByteArray) (event : Driver.Event)
    (window : InputWindow received wire) : InputWindow (received ++ eventOctets event) (eventInput wire event) := by
  obtain ⟨consumed, rfl⟩ := window
  refine ⟨consumed, ?_⟩
  cases event <;> simp [eventOctets, eventInput, List.append_assoc]

theorem input_shift_window (cfg : Config) (received : List UInt8) (wire after : ByteArray)
    (shift : InputShift cfg wire after) (window : InputWindow received wire) : InputWindow received after := by
  obtain ⟨consumed, partition, _⟩ := input_shift_partition cfg wire after shift
  obtain ⟨earlier, rfl⟩ := window
  refine ⟨earlier ++ consumed.data.toList, ?_⟩
  simp [partition, List.append_assoc]

theorem read_octets_cons (event : Driver.Event) (events : List Driver.Event) :
    LeanUV.TCP.Contract.flatten (LeanUV.TCP.Machine.readEvents (event :: events)) =
      eventOctets event ++ LeanUV.TCP.Contract.flatten (LeanUV.TCP.Machine.readEvents events) := by
  cases event <;> simp [eventOctets, LeanUV.TCP.Machine.readEvents, LeanUV.TCP.Contract.flatten]

/-- The independent ledger proves concrete byte provenance for every handler
command, and an exact consumed-prefix/unconsumed-suffix partition at the end. -/
theorem input_trace_origin (cfg : Config) (wire final : ByteArray) (events : List Driver.Event)
    (commands : List Driver.Command) (trace : InputTrace cfg wire events commands final)
    (received : List UInt8) (window : InputWindow received wire) :
    InputWindow (received ++ LeanUV.TCP.Contract.flatten (LeanUV.TCP.Machine.readEvents events)) final ∧
      ∀ request, .perform (.handle request) ∈ commands →
        InputSegment cfg (received ++ LeanUV.TCP.Contract.flatten (LeanUV.TCP.Machine.readEvents events)) request := by
  induction trace generalizing received with
  | nil wire =>
    exact ⟨by simpa [LeanUV.TCP.Machine.readEvents, LeanUV.TCP.Contract.flatten] using window, by simp⟩
  | next wire after final event command events commands shift valid trace ih =>
    have next := input_shift_window cfg (received ++ eventOctets event) (eventInput wire event) after shift
      (input_event_window received wire event window)
    have tail := ih (received ++ eventOctets event) next
    constructor
    · simpa only [read_octets_cons, List.append_assoc] using tail.1
    · intro request member
      simp only [List.mem_cons] at member
      rcases member with equal | member
      · rw [←equal] at valid
        obtain ⟨rest, grammar⟩ := valid
        obtain ⟨before, partition⟩ := next
        refine ⟨before, after, LeanUV.TCP.Contract.flatten (LeanUV.TCP.Machine.readEvents events), rest, ?_, grammar⟩
        rw [read_octets_cons, ←List.append_assoc, partition]
      · simpa only [read_octets_cons, List.append_assoc] using tail.2 request member

/-- The full receive/consume trace of the deployed UV driver refines InputTrace. -/
theorem driver_native_input_trace (cfg : Config) (events : List Driver.Event)
    (final : Driver.State) (commands : List Driver.Command)
    (execution : LeanUV.TCP.Machine.ExecutionContract (Driver.machine cfg) events final commands Driver.EffectShape) :
    ∃ finalWire, InputState cfg finalWire final ∧ InputTrace cfg .empty events commands finalWire := by
  have h := driver_replay_input cfg .empty (Driver.machine cfg).initial events (input_initial cfg)
  rw [execution.refinement] at h
  exact h

/-- Every delivered Request comes from a contiguous, unchanged portion of the
actual native network input. Its complete fields, binary body and remainder are
proved by RequestWire; none is assumed from the FFI or application. -/
theorem driver_native_input_origin (cfg : Config) (events : List Driver.Event)
    (final : Driver.State) (commands : List Driver.Command)
    (native : LeanUV.TCP.Contract.Observation) (invoked : List Driver.Work)
    (execution : LeanUV.TCP.Machine.ExecutionContract (Driver.machine cfg) events final commands Driver.EffectShape)
    (adapter : LeanUV.TCP.Machine.AdapterContract events commands native invoked)
    (transport : LeanUV.TCP.Contract.NativeContract native) :
    ∀ request, .perform (.handle request) ∈ commands → InputSegment cfg native.networkInput request := by
  obtain ⟨finalWire, _, trace⟩ := driver_native_input_trace cfg events final commands execution
  have origin := (input_trace_origin cfg .empty finalWire events commands trace [] ⟨[], rfl⟩).2
  obtain ⟨later, network⟩ := LeanUV.TCP.Machine.adapter_input_prefix events commands native invoked adapter transport
  intro request member
  obtain ⟨before, wire, after, rest, partition, grammar⟩ := origin request member
  refine ⟨before, wire, after ++ later, rest, ?_, grammar⟩
  simp only [List.nil_append] at partition
  rw [network, partition]
  simp only [List.append_assoc]

end FastHTTP.Protocol
