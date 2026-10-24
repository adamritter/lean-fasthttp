import Bench.Baseline

private def prepared (body : ByteArray) (status := 200) (reason := "OK") : IO BaselineHTTP.Response :=
  IO.ofExcept ((BaselineHTTP.Response.create body status reason).mapError IO.userError)

def main (args : List String) : IO Unit := do
  let port := (args[0]?.getD "18095").toNat?.getD 0
  unless port > 0 && port < 65536 do throw (IO.userError "usage: fast_http [port:1..65535]")
  -- Allocate and serialize the benchmark payload once, before accepting clients.
  let response ← prepared (String.ofList (List.replicate 1024 'x')).toUTF8
  let missing ← prepared "Not found\n".toUTF8 404 "Not Found"
  IO.println s!"FastHTTP: 127.0.0.1:{port}, 1024 bytes, request handler + async I/O"
  BaselineHTTP.serve (.v4 ⟨.ofParts 127 0 0 1, port.toUInt16⟩) fun request => do
    if request.targetIs "/" then return .ready response
    else return .ready missing
