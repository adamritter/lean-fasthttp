import Tests.Handlers

def main (args : List String) : IO Unit := do
  let port := (args[0]?.getD "18096").toNat?.getD 18096
  FastHTTP.serve (.v4 ⟨.ofParts 127 0 0 1, port.toUInt16⟩) (← Tests.makeHandler)
