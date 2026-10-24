import FastHTTP.ResponseProofs
import FastHTTP.DriverNativeProofs

namespace FastHTTP.Protocol

set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

def PurposeOutput (purpose : Driver.Purpose) (wire : List UInt8) : Prop :=
  match purpose with
  | .rejection => PreparedOutputGrammar true false false wire
  | .response request _ => PreparedOutputGrammar request.close request.isHead (request.versionMinor == 0) wire

def PreparedCommand (purpose : Driver.Purpose) (command : Driver.Command) : Prop :=
  ∃ buffers, command = .write buffers ∧ PurposeOutput purpose (wireBytes buffers)

/-- The pending command gives each streaming phase its protocol meaning. A HEAD
stream cannot enter a producer/body phase. The terminal chunk has its own write
acknowledgment, so another request cannot overtake it. -/
def StreamOutput (stream : Driver.Streaming) (command : Driver.Command) : Prop :=
  match stream.control.phase with
  | .headers => ∃ buffers, command = .write buffers ∧
      StreamingOutputGrammar stream.request.close (stream.request.versionMinor == 0) (wireBytes buffers)
  | .producer => stream.request.isHead = false ∧
      (command = .perform (.produce stream.response.next) ∨ ∃ promise, command = .perform (.chunk promise))
  | .chunkWrite => stream.request.isHead = false ∧ ∃ payload,
      payload.isEmpty = false ∧ command = .write (if stream.request.versionMinor == 0 then #[payload] else encodeChunk payload) ∧
      ChunkOutputGrammar payload (wireBytes (encodeChunk payload))
  | .endWrite => stream.request.isHead = false ∧ stream.request.versionMinor ≠ 0 ∧ command = .write #["0\r\n\r\n".toUTF8]
  | .done => command = .idle

/-- Every actual phase carries the only pending effects/wire productions allowed
there. Cleanup stores a certified continuation and emits it only after release. -/
def OutputPair : Driver.State → Driver.Command → Prop
  | .reading _, command => command = .idle
  | .continuing _, command => command = .write #["HTTP/1.1 100 Continue\r\n\r\n".toUTF8]
  | .handling request _, command => command = .perform (.handle request) ∨ ∃ promise, command = .perform (.response promise)
  | .preparing _ _, command => command = .perform .date
  | .streamDate stream, command => command = .perform .date ∧ stream.control.phase = .headers
  | .sending purpose, command => PreparedCommand purpose command
  | .streaming stream, command => StreamOutput stream command
  | .releasing next pending, command => (∃ action, command = .finalize (.release action)) ∧ OutputPair next pending
  | .closed, command => command = .idle ∨ command = .shutdown ∨ command = .abort

theorem output_reject (status : Nat) : OutputPair (Driver.reject status).1 (Driver.reject status).2 := by
  unfold Driver.reject
  repeat' first | split | dsimp only
  all_goals simp [OutputPair]

theorem output_accept (step : Step) : OutputPair (Driver.accept step).1 (Driver.accept step).2 := by
  cases step <;> simp only [Driver.accept]
  all_goals first | exact output_reject _ | simp [OutputPair]

theorem output_resume (cfg : Config) (purpose : Driver.Purpose) :
    OutputPair (Driver.resume cfg purpose).1 (Driver.resume cfg purpose).2 := by
  cases purpose <;> simp only [Driver.resume]
  all_goals repeat' first | split | dsimp only
  all_goals first | exact output_accept _ | simp [OutputPair]

theorem output_stop (state : Driver.State) (command : Driver.Command)
    (terminal : OutputPair .closed command) : OutputPair (Driver.stop state command).1 (Driver.stop state command).2 := by
  cases state <;> simp only [Driver.stop]
  all_goals try split
  all_goals first | exact terminal | exact ⟨⟨_, rfl⟩, terminal⟩

def StreamCommandOutput (stream : Driver.Streaming) : StreamCommand → Prop
  | .idle => StreamOutput stream .idle
  | .pull => StreamOutput stream (.perform (.produce stream.response.next))
  | .write buffers => StreamOutput stream (.write buffers)
  | .resume | .finish | .abort => True

theorem output_stream_command (cfg : Config) (stream : Driver.Streaming) (command : StreamCommand)
    (valid : StreamCommandOutput stream command) :
    OutputPair (Driver.streamCommand cfg stream command).1 (Driver.streamCommand cfg stream command).2 := by
  cases command <;> simp only [Driver.streamCommand]
  all_goals first | exact valid | exact output_resume cfg _ | simp [OutputPair]

/-- External event enabling is purely about outstanding writes and producer jobs. -/
def StreamEventEnabled (stream : Driver.Streaming) : StreamEvent → Prop
  | .written => stream.control.phase = .headers ∨ stream.control.phase = .chunkWrite ∨ stream.control.phase = .endWrite
  | .chunk _ | .eof => stream.control.phase = .producer
  | .failed | .closed => True

def StreamHeadSafe (stream : Driver.Streaming) : Prop :=
  stream.request.isHead = true → stream.control.phase = .headers ∨ stream.control.phase = .done

theorem output_stream_head_safe (stream : Driver.Streaming) (command : Driver.Command)
    (valid : StreamOutput stream command) : StreamHeadSafe stream := by
  cases phase : stream.control.phase <;> simp_all [StreamOutput, StreamHeadSafe]

theorem output_stream_written_enabled (stream : Driver.Streaming) (command : Driver.Command)
    (valid : StreamOutput stream command) (allowed : LeanUV.TCP.Machine.permitted command (.written : Driver.Event)) :
    StreamEventEnabled stream .written := by
  cases phase : stream.control.phase <;> simp_all [StreamOutput, StreamEventEnabled]
  · rcases valid.2 with rfl | ⟨promise, rfl⟩ <;> contradiction
  · subst command
    contradiction

theorem output_stream_result_enabled (stream : Driver.Streaming) (command : Driver.Command) (result : Driver.Result)
    (valid : StreamOutput stream command) (allowed : LeanUV.TCP.Machine.permitted command (.result result)) :
    stream.control.phase = .producer := by
  cases phase : stream.control.phase <;> simp_all [StreamOutput]
  · obtain ⟨buffers, rfl, _⟩ := valid
    contradiction
  · obtain ⟨_, payload, _, rfl, _⟩ := valid
    contradiction
  · obtain ⟨_, _, rfl⟩ := valid
    contradiction
  · subst command
    contradiction

/-- Stream framing and phase progression are proved against the grammar of the
actual emitted bytes. No application result is assumed to be a valid chunk. -/
theorem output_stream_step (stream : Driver.Streaming) (event : StreamEvent)
    (enabled : StreamEventEnabled stream event) (headSafe : StreamHeadSafe stream) :
    StreamCommandOutput { stream with control := (streamStep stream.request stream.control event).state }
      (streamStep stream.request stream.control event).command := by
  cases stream with
  | mk request rest response control =>
    cases control with
    | mk phase owns =>
      cases event with
      | written =>
        cases phase <;> cases hh : request.isHead <;>
          simp_all [StreamEventEnabled, StreamHeadSafe, streamStep, streamStop, StreamCommandOutput, StreamOutput]
      | eof =>
        cases phase <;> by_cases legacy : request.versionMinor = 0 <;> cases hh : request.isHead <;>
          simp_all [StreamEventEnabled, StreamHeadSafe, streamStep, streamStop, StreamCommandOutput, StreamOutput]
      | chunk bytes =>
        cases phase <;> cases empty : bytes.isEmpty <;> by_cases legacy : request.versionMinor = 0 <;> cases hh : request.isHead <;>
          simp_all [StreamEventEnabled, StreamHeadSafe, streamStep, streamStop, StreamCommandOutput, StreamOutput]
        all_goals exact ⟨bytes, empty, rfl, encoded_chunk_grammar bytes empty⟩
      | failed => cases phase <;>
          simp_all [StreamEventEnabled, StreamHeadSafe, streamStep, streamStop, StreamCommandOutput, StreamOutput]
      | closed => cases phase <;>
          simp_all [StreamEventEnabled, StreamHeadSafe, streamStep, streamStop, StreamCommandOutput, StreamOutput]

theorem output_stream_event (cfg : Config) (stream : Driver.Streaming) (event : StreamEvent)
    (enabled : StreamEventEnabled stream event) (headSafe : StreamHeadSafe stream) :
    OutputPair (Driver.streamEvent cfg stream event).1 (Driver.streamEvent cfg stream event).2 := by
  have valid := output_stream_command cfg { stream with control := (streamStep stream.request stream.control event).state }
    (streamStep stream.request stream.control event).command (output_stream_step stream event enabled headSafe)
  unfold Driver.streamEvent
  dsimp only
  split
  · exact ⟨⟨_, rfl⟩, valid⟩
  · exact valid

/-- Every causally scheduled transition of the deployed controller preserves
response grammar, HEAD suppression and phase/command order. -/
theorem driver_step_output (cfg : Config) (state : Driver.State) (prior : Driver.Command) (event : Driver.Event)
    (valid : OutputPair state prior) (allowed : LeanUV.TCP.Machine.permitted prior event)
    (effect : LeanUV.TCP.Machine.effectMatches Driver.EffectShape prior event) :
    OutputPair (Driver.step cfg state event).1 (Driver.step cfg state event).2 := by
  cases event with
  | closed => exact output_stop state .idle (Or.inl rfl)
  | failed => exact output_stop state .abort (Or.inr (Or.inr rfl))
  | data bytes =>
    cases state <;> simp only [Driver.step]
    all_goals first | exact output_accept _ | exact output_stop _ .abort (Or.inr (Or.inr rfl)) | simp [OutputPair]
  | written =>
    cases state <;> simp only [Driver.step]
    all_goals try first | exact output_accept _ | exact output_resume cfg _ |
      exact output_stop _ .abort (Or.inr (Or.inr rfl)) | simp [OutputPair]
    exact output_stream_event cfg _ .written (output_stream_written_enabled _ prior valid allowed)
      (output_stream_head_safe _ prior valid)
  | result result =>
    cases state <;> cases result <;> simp only [Driver.step]
    all_goals try first | exact output_stop _ .abort (Or.inr (Or.inr rfl)) |
      exact output_reject 500 | exact valid.2 | simp [OutputPair]
    case handling.handled request rest reply => cases reply <;> simp [OutputPair]
    case preparing.date purpose response date =>
      exact ⟨_, rfl, driver_prepared_buffers_grammar purpose response date⟩
    case streamDate.date stream date =>
      simp only [OutputPair, StreamOutput, valid.2]
      exact ⟨_, rfl, streaming_buffers_grammar stream.response date _ _⟩
    case streaming.producer stream promise =>
      have phase := output_stream_result_enabled stream prior _ valid allowed
      have headSafe := output_stream_head_safe stream prior valid
      simp_all [OutputPair, StreamOutput, StreamHeadSafe]
    case streaming.chunk stream bytes =>
      have phase := output_stream_result_enabled stream prior _ valid allowed
      have headSafe := output_stream_head_safe stream prior valid
      cases bytes <;> exact output_stream_event cfg stream _ phase headSafe
    case streaming.failed stream =>
      exact output_stream_event cfg stream .failed trivial (output_stream_head_safe stream prior valid)


/-- Every prefix, not just the final state, has the proved phase/command meaning. -/
theorem driver_replay_output (cfg : Config) (state : Driver.State) (prior : Driver.Command)
    (events : List Driver.Event) (valid : OutputPair state prior)
    (schedule : LeanUV.TCP.Machine.scheduled (Driver.machine cfg) Driver.EffectShape state prior events) :
    OutputPair ((Driver.machine cfg).replay state events).1
      (((Driver.machine cfg).replay state events).2.getLastD prior) :=
  LeanUV.TCP.Machine.scheduled_invariant (Driver.machine cfg) Driver.EffectShape OutputPair
    (driver_step_output cfg) state prior valid events schedule

theorem driver_output_prefixes (cfg : Config) (state : Driver.State) (prior : Driver.Command)
    (events : List Driver.Event) (valid : OutputPair state prior)
    (schedule : LeanUV.TCP.Machine.scheduled (Driver.machine cfg) Driver.EffectShape state prior events) :
    ∀ before after, events = before ++ after →
      OutputPair ((Driver.machine cfg).replay state before).1
        (((Driver.machine cfg).replay state before).2.getLastD prior) := by
  intro before
  induction before generalizing state prior events with
  | nil => intro after _; exact valid
  | cons event before ih =>
    intro after equal
    subst events
    have next := driver_step_output cfg state prior event valid schedule.1 schedule.2.1
    have tail := ih (Driver.step cfg state event).1 (Driver.step cfg state event).2
      (before ++ after) next schedule.2.2 after rfl
    simpa [LeanUV.TCP.Machine.replay, Driver.machine, List.getLast?_cons] using tail

/-- The native run has grammatical output and the correct outstanding operation
at every observation prefix. Together with scheduling this excludes response
interleaving: reads occur only at idle, and written only after the pending write. -/
theorem driver_native_output_order (cfg : Config) (events : List Driver.Event)
    (final : Driver.State) (commands : List Driver.Command)
    (execution : LeanUV.TCP.Machine.ExecutionContract (Driver.machine cfg) events final commands Driver.EffectShape) :
    ∀ before after, events = before ++ after →
      OutputPair ((Driver.machine cfg).replay .reading before).1
        (((Driver.machine cfg).replay .reading before).2.getLastD .idle) :=
  driver_output_prefixes cfg .reading .idle events rfl execution.scheduling

/-- Only a completed final/HEAD write can resume a streaming pipeline. -/
theorem stream_resume_gate (request : Request) (state : StreamState) (event : StreamEvent)
    (resume : (streamStep request state event).command = .resume) :
    event = .written ∧ (state.phase = .endWrite ∨ (state.phase = .headers ∧ request.isHead = true)) := by
  cases state with
  | mk phase owns =>
    cases phase <;> cases event <;> cases hh : request.isHead <;>
      simp_all [streamStep, streamStop]
    all_goals repeat' split at resume <;> simp_all

def HandlerGate (state : Driver.State) (event : Driver.Event) : Prop :=
  match state, event with
  | .reading _, .data _ | .continuing _, .written | .sending _, .written | .releasing _ _, .result .released => True
  | .streaming stream, .written => stream.control.phase = .endWrite ∨
      (stream.control.phase = .headers ∧ stream.request.isHead = true)
  | _, _ => False

theorem reject_ne_handler (status : Nat) (request : Request) :
    (Driver.reject status).2 ≠ .perform (.handle request) := by
  unfold Driver.reject
  repeat' first | split | dsimp only
  all_goals simp

theorem stop_ne_handler (state : Driver.State) (command : Driver.Command) (request : Request)
    (notHandler : command ≠ .perform (.handle request)) :
    (Driver.stop state command).2 ≠ .perform (.handle request) := by
  cases state <;> simp [Driver.stop]
  all_goals try split
  all_goals simp_all

theorem stream_command_handler (cfg : Config) (stream : Driver.Streaming) (command : StreamCommand) (request : Request)
    (handler : (Driver.streamCommand cfg stream command).2 = .perform (.handle request)) : command = .resume := by
  cases command <;> simp_all [Driver.streamCommand]

theorem stream_event_handler (cfg : Config) (stream : Driver.Streaming) (event : StreamEvent) (request : Request)
    (handler : (Driver.streamEvent cfg stream event).2 = .perform (.handle request)) :
    event = .written ∧ (stream.control.phase = .endWrite ∨
      (stream.control.phase = .headers ∧ stream.request.isHead = true)) := by
  unfold Driver.streamEvent at handler
  dsimp only at handler
  split at handler
  · contradiction
  · exact stream_resume_gate stream.request stream.control event (stream_command_handler cfg _ _ request handler)

/-- Every actual handler invocation is gated by input reception, a completed
Expect/final-response write, or the finalizer forwarding a stored continuation.
There is no handler path out of an outstanding handler/producer/body write. -/
theorem driver_handler_gate (cfg : Config) (state : Driver.State) (event : Driver.Event) (request : Request)
    (handler : (Driver.step cfg state event).2 = .perform (.handle request)) : HandlerGate state event := by
  cases event with
  | closed => exact False.elim (stop_ne_handler state .idle request (by simp) handler)
  | failed => exact False.elim (stop_ne_handler state .abort request (by simp) handler)
  | data bytes =>
    cases state <;> simp only [Driver.step] at handler <;> simp only [HandlerGate]
    all_goals first | trivial | contradiction | exact False.elim (stop_ne_handler _ .abort request (by simp) handler)
  | written =>
    cases state <;> simp only [Driver.step] at handler <;> simp only [HandlerGate]
    all_goals first
      | trivial
      | contradiction
      | exact False.elim (stop_ne_handler _ .abort request (by simp) handler)
      | exact (stream_event_handler cfg _ .written request handler).2
  | result result =>
    cases state <;> cases result <;> simp only [Driver.step] at handler <;> simp only [HandlerGate]
    all_goals try first
      | trivial
      | contradiction
      | exact False.elim (stop_ne_handler _ .abort request (by simp) handler)
      | exact False.elim (reject_ne_handler 500 request handler)
    all_goals try simp at handler
    case handling.handled current rest reply => cases reply <;> simp at handler
    case streaming.chunk stream bytes =>
      cases bytes <;> have h := (stream_event_handler cfg stream _ request handler).1 <;> contradiction
    case streaming.failed stream =>
      have h := (stream_event_handler cfg stream .failed request handler).1
      contradiction

end FastHTTP.Protocol
