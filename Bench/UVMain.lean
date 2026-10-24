import FastHTTP.UV

private def prepared (body : ByteArray) (status := 200) (reason := "OK") : IO FastHTTP.Response :=
  IO.ofExcept ((FastHTTP.Response.create body status reason).mapError IO.userError)

def main (args : List String) : IO Unit := do
  let port := (args[0]?.getD "18098").toNat?.getD 0
  let workers := (args[1]?.getD "4").toNat?.getD 0
  let cpu := (args[2]?.getD "4294967295").toNat?.getD 4294967295
  unless port > 0 && port < 65536 && workers > 0 && workers ≤ 256 do
    throw (IO.userError "usage: uv_http [port] [workers:1..256] [first_cpu]")
  let stats ← FastHTTP.UV.serve {
    port := port.toUInt16, threads := workers.toUInt32
    firstCpu := if cpu == 4294967295 then none else some cpu.toUInt32 } fun _ => do
      let response ← prepared (String.ofList (List.replicate 1024 'x')).toUTF8
      let missing ← prepared "Not found\n".toUTF8 404 "Not Found"
      return fun request => pure (.ready (if request.targetIs "/" then response else missing))
  for i in [:stats.size] do
    let s := stats[i]!
    IO.println s!"worker={i} accepted={s.accepted} reads={s.readCallbacks} sends={s.sendCalls} bytes={s.sentBytes} queued={s.queuedWrites} errors={s.errors} peer_disconnects={s.peerDisconnects} elapsed_ns={s.elapsedNs}"
