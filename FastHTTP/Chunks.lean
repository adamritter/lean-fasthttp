import FastHTTP.Lexical

namespace FastHTTP.Protocol

/-- Parse one chunk extension. The no-value branch leaves trailing BWS for
 the next semicolon, so bare trailing whitespace is never accepted. -/
def chunkExtension (line : ByteArray) (start : Nat) : Option Nat :=
  let semi := spanEnd line line.size space start
  if semi ≥ line.size || line[semi]! != 59 then none
  else
    let key := spanEnd line line.size space (semi + 1)
    let nameEnd := spanEnd line line.size token key
    if nameEnd == key then none
    else
      let eq := spanEnd line line.size space nameEnd
      if eq < line.size && line[eq]! == 61 then
        let value := spanEnd line line.size space (eq + 1)
        if value < line.size && line[value]! == 34 then quotedEnd line value line.size
        else
          let last := spanEnd line line.size token value
          if last == value then none else some last
      else some nameEnd

/-- Complete extension suffix. Strict progress is checked before recursion. -/
def chunkExtensions (line : ByteArray) (start : Nat) : Except Nat Unit :=
  if start = line.size then .ok ()
  else if start > line.size then .error 400
  else match chunkExtension line start with
    | none => .error 400
    | some last =>
      if last ≤ start then .error 400 else chunkExtensions line last
termination_by line.size - start

end FastHTTP.Protocol
