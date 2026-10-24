import FastHTTP.DriverProofs
import LeanUV.AdapterContract

namespace FastHTTP.Protocol

def driverFinalizerWeight : Driver.Work → Nat
  | .release _ => 1
  | _ => 0

theorem driver_finalizer_weight (command : Driver.Command) :
    LeanUV.TCP.Machine.finalizerWeight driverFinalizerWeight command = driverReleaseUnits command := by
  cases command <;> try rfl
  rename_i work
  cases work <;> rfl

/-- Actual release invocations, not merely queued commands, conserve all adopted
stream cleanup rights. Both generic IO refinement premises are visible. The
application cleanup action's internal resource semantics are not assumed here. -/
theorem driver_actual_cleanup (cfg : Config) (events : List Driver.Event)
    (final : Driver.State) (commands : List Driver.Command)
    (native : LeanUV.TCP.Contract.Observation) (invoked : List Driver.Work)
    (execution : LeanUV.TCP.Machine.ExecutionContract (Driver.machine cfg) events final commands Driver.EffectShape)
    (adapter : LeanUV.TCP.Machine.AdapterContract events commands native invoked) :
    (invoked.map driverFinalizerWeight).sum + driverOwned final = driverAcquiredTrace cfg .reading events := by
  have actual := LeanUV.TCP.Machine.adapter_finalizer_weight events commands native invoked driverFinalizerWeight adapter
  have weight : LeanUV.TCP.Machine.finalizerWeight driverFinalizerWeight = driverReleaseUnits :=
    funext driver_finalizer_weight
  rw [weight] at actual
  rw [actual]
  exact (driver_native_resource cfg events final commands execution).2

theorem driver_actual_cleanup_complete (cfg : Config) (events : List Driver.Event)
    (final : Driver.State) (commands : List Driver.Command)
    (native : LeanUV.TCP.Contract.Observation) (invoked : List Driver.Work)
    (execution : LeanUV.TCP.Machine.ExecutionContract (Driver.machine cfg) events final commands Driver.EffectShape)
    (adapter : LeanUV.TCP.Machine.AdapterContract events commands native invoked)
    (released : driverOwned final = 0) :
    (invoked.map driverFinalizerWeight).sum = driverAcquiredTrace cfg .reading events := by
  simpa only [released, Nat.add_zero] using driver_actual_cleanup cfg events final commands native invoked execution adapter

/-- An interrupted native connection can emit only a prefix of the exact pure
HTTP controller's selected output. The transport and adapter assumptions contain
no HTTP parser or serialization correctness predicate. -/
theorem driver_actual_output_prefix (cfg : Config) (events : List Driver.Event)
    (final : Driver.State) (commands : List Driver.Command)
    (native : LeanUV.TCP.Contract.Observation) (invoked : List Driver.Work)
    (execution : LeanUV.TCP.Machine.ExecutionContract (Driver.machine cfg) events final commands Driver.EffectShape)
    (adapter : LeanUV.TCP.Machine.AdapterContract events commands native invoked)
    (transport : LeanUV.TCP.Contract.NativeContract native) :
    LeanUV.TCP.Contract.Prefix native.transportOutput
      (LeanUV.TCP.Machine.commandBytes ((Driver.machine cfg).replay (Driver.machine cfg).initial events).2) := by
  rw [execution.refinement]
  exact LeanUV.TCP.Machine.adapter_output_prefix events commands native invoked adapter transport

/-- Successful graceful shutdown drains exactly the pure controller's selected
bytes. This does not assert that a remote application has consumed those bytes. -/
theorem driver_actual_graceful_output (cfg : Config) (events : List Driver.Event)
    (final : Driver.State) (commands : List Driver.Command)
    (native : LeanUV.TCP.Contract.Observation) (invoked : List Driver.Work)
    (execution : LeanUV.TCP.Machine.ExecutionContract (Driver.machine cfg) events final commands Driver.EffectShape)
    (adapter : LeanUV.TCP.Machine.AdapterContract events commands native invoked)
    (transport : LeanUV.TCP.Contract.NativeContract native)
    (graceful : native.closeReason = some .graceful) :
    native.transportOutput =
      LeanUV.TCP.Machine.commandBytes ((Driver.machine cfg).replay (Driver.machine cfg).initial events).2 := by
  rw [execution.refinement]
  exact LeanUV.TCP.Machine.adapter_graceful_output events commands native invoked adapter transport graceful

end FastHTTP.Protocol
