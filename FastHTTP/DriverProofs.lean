import FastHTTP.Driver
import FastHTTP.MessageGrammarProofs
import FastHTTP.StreamMachineProofs

namespace FastHTTP.Protocol

set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

/-- The single cleanup right held by the connection. A finalizer is executed
without yielding after it is issued; releasing states have already spent it. -/
def driverOwned : Driver.State → Nat
  | .streamDate stream | .streaming stream => cleanupUnits stream.control.ownsResource
  | _ => 0

def driverReleaseUnits : Driver.Command → Nat
  | .finalize (.release _) => 1
  | _ => 0

def DriverWellFormed : Driver.State → Prop
  | .releasing next command => DriverWellFormed next ∧ driverOwned next = 0 ∧ driverReleaseUnits command = 0
  | _ => True

/-- Acquisition is the exact event that adopts an application's stream. A
late/mismatched result cannot create a new cleanup right. -/
def driverAcquired : Driver.State → Driver.Event → Nat
  | .handling _ _, .result (.handled (.streaming _)) => 1
  | _, _ => 0

def DriverEmpty (pair : Driver.State × Driver.Command) : Prop :=
  DriverWellFormed pair.1 ∧ driverOwned pair.1 = 0 ∧ driverReleaseUnits pair.2 = 0

theorem driver_reject_empty (status : Nat) : DriverEmpty (Driver.reject status) := by
  unfold DriverEmpty Driver.reject
  repeat' first | split | dsimp only
  all_goals simp [DriverEmpty, DriverWellFormed, driverOwned, driverReleaseUnits]

theorem driver_accept_empty (step : Step) : DriverEmpty (Driver.accept step) := by
  cases step <;> simp [Driver.accept, DriverEmpty, DriverWellFormed, driverOwned, driverReleaseUnits]
  exact driver_reject_empty _

theorem driver_resume_empty (cfg : Config) (purpose : Driver.Purpose) : DriverEmpty (Driver.resume cfg purpose) := by
  cases purpose with
  | rejection => simp [Driver.resume, DriverEmpty, DriverWellFormed, driverOwned, driverReleaseUnits]
  | response request rest =>
    simp only [Driver.resume]
    split
    · simp [DriverEmpty, DriverWellFormed, driverOwned, driverReleaseUnits]
    · split
      · simp [DriverEmpty, DriverWellFormed, driverOwned, driverReleaseUnits]
      · exact driver_accept_empty _

/-- The actual stream adapter preserves the cleanup accounting of streamStep,
including the continuation after finalization and the next pipeline request. -/
theorem driver_stream_resource (cfg : Config) (stream : Driver.Streaming) (event : StreamEvent) :
    DriverWellFormed (Driver.streamEvent cfg stream event).1 ∧
      driverReleaseUnits (Driver.streamEvent cfg stream event).2 + driverOwned (Driver.streamEvent cfg stream event).1 =
        cleanupUnits stream.control.ownsResource := by
  have resume := driver_resume_empty cfg (.response stream.request stream.rest)
  rcases resume with ⟨resumeWF, resumeOwned, resumeRelease⟩
  cases hp : stream.control.phase <;> cases event <;> cases ho : stream.control.ownsResource <;>
    simp [Driver.streamEvent, streamStep, streamStop, hp, ho, Driver.streamCommand,
      DriverWellFormed, driverOwned, driverReleaseUnits, cleanupUnits, resumeWF, resumeOwned, resumeRelease]
  all_goals repeat' split
  all_goals simp_all [DriverWellFormed, driverOwned, driverReleaseUnits, cleanupUnits]
  all_goals grind

theorem driver_stop_resource (state : Driver.State) (command : Driver.Command)
    (hc : driverReleaseUnits command = 0) :
    DriverWellFormed (Driver.stop state command).1 ∧
      driverReleaseUnits (Driver.stop state command).2 + driverOwned (Driver.stop state command).1 = driverOwned state := by
  cases state <;> simp [Driver.stop, DriverWellFormed, driverOwned, driverReleaseUnits, cleanupUnits, hc]
  all_goals split <;> simp_all [DriverWellFormed, driverOwned, driverReleaseUnits]

/-- Every actual controller transition conserves cleanup rights, including
arbitrary failed, closed, duplicate and out-of-order events. -/
theorem driver_step_resource (cfg : Config) (state : Driver.State) (event : Driver.Event)
    (wf : DriverWellFormed state) :
    DriverWellFormed (Driver.step cfg state event).1 ∧
      driverReleaseUnits (Driver.step cfg state event).2 + driverOwned (Driver.step cfg state event).1 =
        driverOwned state + driverAcquired state event := by
  cases event with
  | closed =>
    cases state <;> simp only [Driver.step, driverAcquired, Nat.add_zero]
    all_goals exact driver_stop_resource _ .idle rfl
  | failed =>
    cases state <;> simp only [Driver.step, driverAcquired, Nat.add_zero]
    all_goals exact driver_stop_resource _ .abort rfl
  | data bytes =>
    cases state <;> simp only [Driver.step, driverAcquired, Nat.add_zero]
    · rename_i parser
      have h := driver_accept_empty (feed cfg parser bytes); exact ⟨h.1, by rw [h.2.1, h.2.2]; rfl⟩
    all_goals first | exact driver_stop_resource _ .abort rfl | simp [DriverWellFormed, driverOwned, driverReleaseUnits]
  | written =>
    cases state <;> simp only [Driver.step, driverAcquired, Nat.add_zero]
    · exact driver_stop_resource _ .abort rfl
    · rename_i parser
      have h := driver_accept_empty (feed cfg parser .empty); exact ⟨h.1, by rw [h.2.1, h.2.2]; rfl⟩
    · exact driver_stop_resource _ .abort rfl
    · exact driver_stop_resource _ .abort rfl
    · rename_i purpose
      have h := driver_resume_empty cfg purpose; exact ⟨h.1, by rw [h.2.1, h.2.2]; rfl⟩
    · exact driver_stop_resource _ .abort rfl
    · exact driver_stream_resource cfg _ .written
    · exact driver_stop_resource _ .abort rfl
    · simp [DriverWellFormed, driverOwned, driverReleaseUnits]
  | result result =>
    cases state <;> cases result <;> simp only [Driver.step, driverAcquired, Nat.add_zero]
    all_goals first
      | exact driver_stop_resource _ .abort rfl
      | exact driver_stream_resource cfg _ _
      | simp [DriverWellFormed, driverOwned, driverReleaseUnits, cleanupUnits]
    all_goals try (have h := driver_reject_empty 500; exact ⟨h.1, by rw [h.2.1, h.2.2]; rfl⟩)
    all_goals try (simp_all [DriverWellFormed, driverOwned, driverReleaseUnits])
    case handling.handled request rest reply =>
      cases reply <;> simp [DriverWellFormed, driverOwned, driverReleaseUnits, cleanupUnits, driverAcquired]
    case handling.failed =>
      have h := driver_reject_empty 500
      simpa [DriverEmpty, driverOwned, driverReleaseUnits, cleanupUnits, and_comm, and_left_comm] using h
    case streaming.chunk stream bytes =>
      cases bytes <;> exact driver_stream_resource cfg stream _
    case releasing.released next command =>
      simpa [cleanupUnits] using wf.2.1

def driverAcquiredTrace (cfg : Config) (state : Driver.State) : List Driver.Event → Nat
  | [] => 0
  | event :: events => driverAcquired state event + driverAcquiredTrace cfg (Driver.step cfg state event).1 events

/-- Conservation for the exact command log produced by the complete reactor.
This counts adopted stream instances, not just an isolated stream component. -/
theorem driver_replay_resource (cfg : Config) (state : Driver.State) (events : List Driver.Event)
    (wf : DriverWellFormed state) :
    let replay := LeanUV.TCP.Machine.replay (Driver.machine cfg) state events
    DriverWellFormed replay.1 ∧
      (replay.2.map driverReleaseUnits).sum + driverOwned replay.1 =
        driverOwned state + driverAcquiredTrace cfg state events := by
  induction events generalizing state with
  | nil => simpa [LeanUV.TCP.Machine.replay, driverAcquiredTrace] using wf
  | cons event events ih =>
    have step := driver_step_resource cfg state event wf
    have tail := ih (Driver.step cfg state event).1 step.1
    refine ⟨tail.1, ?_⟩
    simp only [LeanUV.TCP.Machine.replay, Driver.machine, driverAcquiredTrace,
      List.map_cons, List.sum_cons]
    have total := tail.2
    have current := step.2
    simp only [Driver.machine] at total current
    omega

/-- Conditional IO transfer for the actual adapter used by FastHTTP.UV. The
explicit hypothesis is lean-uv's generic execution contract; HTTP cleanup
conservation itself is proved above rather than assumed. -/
theorem driver_native_resource (cfg : Config) (events : List Driver.Event)
    (final : Driver.State) (commands : List Driver.Command)
    (execution : LeanUV.TCP.Machine.ExecutionContract (Driver.machine cfg) events final commands Driver.EffectShape) :
    DriverWellFormed final ∧
      (commands.map driverReleaseUnits).sum + driverOwned final = driverAcquiredTrace cfg .reading events := by
  have h := driver_replay_resource cfg .reading events (by trivial)
  have observed := execution.refinement
  change LeanUV.TCP.Machine.replay (Driver.machine cfg) .reading events = (final, commands) at observed
  dsimp only at h
  rw [observed] at h
  simpa only [driverOwned, Nat.zero_add] using h

theorem driver_native_cleanup_at_most_acquired (cfg : Config) (events : List Driver.Event)
    (final : Driver.State) (commands : List Driver.Command)
    (execution : LeanUV.TCP.Machine.ExecutionContract (Driver.machine cfg) events final commands Driver.EffectShape) :
    (commands.map driverReleaseUnits).sum ≤ driverAcquiredTrace cfg .reading events := by
  have h := (driver_native_resource cfg events final commands execution).2
  omega

/-- At a checkpoint with no retained stream, each adopted stream has exactly
one finalizer command. Prompt execution of finalizers is an explicit native
adapter obligation; the external cleanup action's own semantics remain external. -/
theorem driver_native_cleanup_complete (cfg : Config) (events : List Driver.Event)
    (final : Driver.State) (commands : List Driver.Command)
    (execution : LeanUV.TCP.Machine.ExecutionContract (Driver.machine cfg) events final commands Driver.EffectShape)
    (closed : driverOwned final = 0) :
    (commands.map driverReleaseUnits).sum = driverAcquiredTrace cfg .reading events := by
  simpa only [closed, Nat.add_zero] using (driver_native_resource cfg events final commands execution).2

end FastHTTP.Protocol
