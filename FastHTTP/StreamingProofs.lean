import FastHTTP.PendingProofs
import FastHTTP.DriverNativeProofs
import FastHTTP.DriverRequestProofs
import FastHTTP.SSE

namespace FastHTTP

theorem pending_stop_cancels (request : Request) (rest : ByteArray) (pending : Pending)
    (command : Driver.Command) :
    Driver.stop (.waiting request rest pending) command =
      (.releasing .closed command, .finalize (.cancel pending.cancel)) := rfl

theorem pending_stream_adopted (cfg : Config) (request : Request) (rest : ByteArray)
    (pending : Pending) (response : StreamResponse) :
    Driver.step cfg (.waiting request rest pending) (.result (.completed (.streaming response))) =
      (.streamDate ⟨request, rest, response, {}⟩, .perform .date) := rfl

theorem sse_bad_event_rejected (data event : String) (id : Option String) (retry : Option Nat)
    (bad : SSE.singleLine event = false) :
    SSE.Event.encode ⟨data, some event, id, retry⟩ =
      .error "SSE event must be a single line without NUL" := by
  simp [SSE.Event.encode, bad] <;> rfl

end FastHTTP
