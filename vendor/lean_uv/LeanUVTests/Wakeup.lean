import LeanUV
import Std.Sync.Mutex
open LeanUV.TCP

def main (args : List String) : IO Unit := do
  let port := ((args[0]?.getD "18399").toNat?.getD 18399).toUInt16
  let tasks ← Std.Mutex.new (#[] : Array (Task (Except IO.Error Unit)))
  let counts ← Std.Mutex.new (0, 0)
  let stats ← serve { port, threads := 4, runForMs := 600, idleTimeoutMs := 0 } fun _ =>
    pure fun socket => do
      let started ← IO.mkRef false
      let resetClient ← IO.mkRef false
      pure {
        onData := fun bytes => do
          if ← started.get then return
          started.set true
          resetClient.set (bytes == "reset".toUTF8)
          socket.pause
          socket.notify -- before arming; owner cannot dispatch until callback returns
          socket.setWakeup true
          let task ← IO.asTask (prio := .dedicated) do
            for _ in [:1000] do
              for _ in [:8] do socket.notify
              IO.sleep 1
          tasks.atomically do modify (·.push task)
        onWake := do
          counts.atomically do modify fun (w, c) => (w + 1, c)
          if !(← resetClient.get) then socket.send "wake\n".toUTF8
        onClose := counts.atomically do modify fun (w, c) => (w, c + 1) }
  -- Producers retain sockets after workers and uv handles are destroyed.
  let late ← tasks.atomically get
  for task in late do IO.ofExcept (← IO.wait task)
  let (wakes, closed) ← counts.atomically get
  unless wakes > 0 && closed ≥ late.size && late.size > 0 do
    throw (IO.userError s!"invalid counts: {wakes}, {closed}, {late.size}")
  unless stats.all (·.errors == 0) do throw (IO.userError "worker errors")
  IO.println s!"PASS notifications={late.size * 8001} delivered={wakes} closed={closed} late_producers={late.size}"
