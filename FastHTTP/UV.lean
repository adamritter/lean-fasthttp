import FastHTTP.Driver
import LeanUV

/-! FastHTTP's complete protocol and response API on independent lean-uv workers.
The actual socket adapter executes Driver.machine. HTTP decisions are pure;
this module only interprets application, promise, clock and cleanup work. -/
namespace FastHTTP.UV

/-- Polling is idempotent. One-shot handler/producer invocations return their
promise before a distinct job starts polling it. Resource-bearing handler
results are adopted by the machine before the native adapter can yield. -/
private def effect (handler : Handler) (dates : DateCache) : Driver.Work → IO (Option Driver.Result)
  | .handle request => do
    try return some (.handled (← handler request)) catch _ => return some .failed
  | .response promise => do
    if !(← IO.hasFinished promise.result?) then return none
    return some (match promise.result?.get with
      | some (.ok response) => .response response
      | _ => .failed)
  | .pending pending => do
    try
      return (← pending.poll).map fun
        | .ok response => .completed response
        | .error _ => .failed
    catch _ => return some .failed
  | .produce next => do
    try return some (.producer (← next)) catch _ => return some .failed
  | .chunk promise => do
    if !(← IO.hasFinished promise.result?) then return none
    return some (match promise.result?.get with
      | some (.ok chunk) => .chunk chunk
      | _ => .failed)
  | .date => do return some (.date (← dates.getChecked))
  | .release action | .cancel action => do
    try action catch _ => pure ()
    return some .released

/-- Handler state and date caches are created on their owning worker. The generic
reactor provides serial callbacks, bounded writes and backpressure. Its explicit
ExecutionContract is the bridge used by the connection-controller proofs. -/
def serve (transport : LeanUV.TCP.Config) (makeHandler : UInt32 → IO Handler)
    (config : Config := {}) : IO (Array LeanUV.TCP.WorkerStats) :=
  LeanUV.TCP.serve transport fun worker => do
    let handler ← makeHandler worker
    let dates ← DateCache.create
    return fun socket =>
      LeanUV.TCP.Machine.callbacks socket (Driver.machine config) (effect handler dates) transport.maxQueuedBytes

end FastHTTP.UV
