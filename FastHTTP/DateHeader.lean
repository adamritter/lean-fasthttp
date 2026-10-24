import FastHTTP.DateSyntaxProofs

namespace FastHTTP

/-- A Date field and final CRLF carrying an erased wire-grammar certificate. -/
structure DateHeader where
  bytes : ByteArray
  grammar : Protocol.DateHeaderGrammar bytes

def DateHeader.create (bytes : ByteArray) : Except String DateHeader :=
  if valid : Protocol.validDateHeader bytes then .ok ⟨bytes, (Protocol.validDateHeader_iff bytes).mp valid⟩
  else .error "clock formatter produced an invalid HTTP Date field"

end FastHTTP
