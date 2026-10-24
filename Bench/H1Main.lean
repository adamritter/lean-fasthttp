import FastHTTP.H1

def main (args : List String) : IO Unit := do
  let port := (args[0]?.getD "18097").toNat?.getD 0
  unless port > 0 && port < 65536 do throw (IO.userError "usage: h1_http [port:1..65535]")
  let response := FastHTTP.H1.Response.bytes (String.ofList (List.replicate 1024 'x')).toUTF8
  let missing := FastHTTP.H1.Response.bytes "Not found\n".toUTF8 .notFound
  IO.println s!"FastHTTP.H1: 127.0.0.1:{port}, 1024 bytes, Std H1 + direct UV"
  FastHTTP.H1.serve (.v4 ⟨.ofParts 127 0 0 1, port.toUInt16⟩) fun request => do
    if toString request.head.uri == "/" then return .ready response
    return .ready missing
