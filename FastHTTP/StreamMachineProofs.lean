import FastHTTP.StreamMachine
import Std.Tactic

namespace FastHTTP.Protocol

/-- Resource ownership is conserved: releasing consumes the single cleanup
right, and no event can recreate it, including late or repeated callbacks. -/
theorem streamStep_resource (request : Request) (state : StreamState) (event : StreamEvent) :
    (if (streamStep request state event).release then 1 else 0) +
      (if (streamStep request state event).state.ownsResource then 1 else 0) =
        (if state.ownsResource then 1 else 0) := by
  cases state with
  | mk phase owns =>
    cases phase <;> cases event <;> simp [streamStep, streamStop]
    all_goals repeat' split <;> simp_all

theorem streamStep_done (request : Request) (state : StreamState) (event : StreamEvent)
    (h : state.phase = .done) : streamStep request state event = ⟨state, false, .idle⟩ := by
  simp [streamStep, h]

/-- A producer is pulled only after a successful write callback. -/
theorem streamStep_pull_after_write (request : Request) (state : StreamState) (event : StreamEvent)
    (h : (streamStep request state event).command = .pull) : event = .written := by
  cases state with
  | mk phase owns =>
    cases phase <;> cases event <;> simp [streamStep, streamStop] at h ⊢
    all_goals repeat' split at h <;> simp_all

/-- Body writes arise only from a producer event while a result is awaited. -/
theorem streamStep_write_from_producer (request : Request) (state : StreamState) (event : StreamEvent)
    (buffers : Array ByteArray) (h : (streamStep request state event).command = .write buffers) :
    state.phase = .producer ∧ (event = .eof ∨ ∃ bytes, event = .chunk bytes) := by
  cases state with
  | mk phase owns =>
    cases phase <;> cases event <;> simp [streamStep, streamStop] at h ⊢
    all_goals repeat' split at h <;> simp_all

/-- HEAD remains in the header/done states and never pulls or emits body bytes. -/
theorem streamStep_head (request : Request) (state : StreamState) (event : StreamEvent)
    (hh : request.isHead = true) (hs : state.phase = .headers ∨ state.phase = .done) :
    ((streamStep request state event).state.phase = .headers ∨
      (streamStep request state event).state.phase = .done) ∧
    (streamStep request state event).command ≠ .pull ∧
    (∀ buffers, (streamStep request state event).command ≠ .write buffers) := by
  cases state with
  | mk phase owns =>
    cases phase <;> cases event <;> simp_all [streamStep, streamStop]

/-- Legacy HTTP/1.0 sends the unmodified payload, without chunk framing. -/
theorem streamStep_legacy_chunk (request : Request) (owns : Bool) (bytes : ByteArray)
    (hv : request.versionMinor = 0) (hb : bytes.isEmpty = false) :
    streamStep request ⟨.producer, owns⟩ (.chunk bytes) =
      ⟨⟨.chunkWrite, owns⟩, false, .write #[bytes]⟩ := by
  simp [streamStep, hv, hb]

/-- HTTP/1.0 EOF closes; it never emits a chunk terminator. -/
theorem streamStep_legacy_eof (request : Request) (owns : Bool) (hv : request.versionMinor = 0) :
    streamStep request ⟨.producer, owns⟩ .eof = ⟨⟨.done, false⟩, owns, .finish⟩ := by
  simp [streamStep, streamStop, hv]

/-- A modern EOF sends exactly one terminator, then awaits its write completion
before allowing the next pipelined request. -/
theorem streamStep_modern_eof (request : Request) (owns : Bool) (hv : request.versionMinor ≠ 0) :
    streamStep request ⟨.producer, owns⟩ .eof =
      ⟨⟨.endWrite, false⟩, owns, .write #["0\r\n\r\n".toUTF8]⟩ := by
  simp [streamStep, hv]

def cleanupUnits (b : Bool) : Nat := if b then 1 else 0

def streamTraceStep (request : Request) (acc : StreamState × Nat) (event : StreamEvent) : StreamState × Nat :=
  let next := streamStep request acc.1 event
  (next.state, acc.2 + cleanupUnits next.release)

/-- Every finite event trace, including duplicated/late/error/close events,
can release a stream resource at most once. -/
theorem streamTrace_resource (request : Request) (events : List StreamEvent) (state : StreamState) (released : Nat) :
    let result := events.foldl (streamTraceStep request) (state, released)
    result.2 + (cleanupUnits result.1.ownsResource) =
      released + (cleanupUnits state.ownsResource) := by
  induction events generalizing state released with
  | nil => rfl
  | cons event events ih =>
    simp only [List.foldl_cons, streamTraceStep]
    rw [ih]
    have step := streamStep_resource request state event
    simp only [cleanupUnits] at *
    omega

theorem streamTrace_release_once (request : Request) (events : List StreamEvent) :
    (events.foldl (streamTraceStep request) ({}, 0)).2 ≤ 1 := by
  have h := streamTrace_resource request events {} 0
  simp only [Nat.zero_add, cleanupUnits, ite_true] at h
  omega

/-- Once a trace has relinquished ownership, cleanup has occurred exactly once. -/
theorem streamTrace_cleanup_complete (request : Request) (events : List StreamEvent)
    (h : (events.foldl (streamTraceStep request) ({}, 0)).1.ownsResource = false) :
    (events.foldl (streamTraceStep request) ({}, 0)).2 = 1 := by
  have conservation := streamTrace_resource request events {} 0
  simpa [cleanupUnits, h] using conservation

def streamCommands (request : Request) (state : StreamState) : List StreamEvent → List StreamCommand
  | [] => []
  | event :: events =>
    let next := streamStep request state event
    next.command :: streamCommands request next.state events

/-- No event trace can make a HEAD stream pull its producer or emit a body. -/
theorem streamCommands_head (request : Request) (state : StreamState) (events : List StreamEvent)
    (hh : request.isHead = true) (hs : state.phase = .headers ∨ state.phase = .done) :
    ∀ command ∈ streamCommands request state events,
      command ≠ .pull ∧ (∀ buffers, command ≠ .write buffers) := by
  induction events generalizing state with
  | nil => simp [streamCommands]
  | cons event events ih =>
    intro command hc
    have step := streamStep_head request state event hh hs
    simp only [streamCommands, List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact step.2
    · exact ih _ step.1 command hc

end FastHTTP.Protocol
