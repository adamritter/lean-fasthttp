import FastHTTP.UV
import Tests.Handlers

def main (args : List String) : IO Unit := do
  let port := (args[0]?.getD "18096").toNat?.getD 18096
  let workers := (args[1]?.getD "1").toNat?.getD 1
  let _ ← FastHTTP.UV.serve { port := port.toUInt16, threads := workers.toUInt32 }
    (fun worker => do
      let handler ← Tests.makeHandler
      return fun request => do
        if request.targetIs "/worker" then
          return .ready (← IO.ofExcept ((FastHTTP.Response.create (toString worker).toUTF8).mapError IO.userError))
        handler request)
