import FastHTTP.Syntax

namespace FastHTTP.Protocol

/-- Maximal bounded span of octets satisfying a predicate. Tail recursive and
allocation-free; the proof gives both the accepted prefix and the first stop. -/
@[specialize] def spanEnd (bytes : ByteArray) (stop : Nat) (accept : UInt8 → Bool) (i : Nat) : Nat :=
  if i < stop && accept bytes[i]! then spanEnd bytes stop accept (i + 1) else i
termination_by stop - i
decreasing_by simp_all; omega

/-- Trim trailing HTTP optional whitespace within an interval. -/
def trimEnd (bytes : ByteArray) (start stop : Nat) : Nat :=
  if start < stop && space bytes[stop - 1]! then trimEnd bytes start (stop - 1) else stop
termination_by stop
decreasing_by simp_all; omega

@[inline] def targetOctet (b : UInt8) : Bool := b >= 33 && b <= 126 && b != 35
@[inline] def fieldOctet (b : UInt8) : Bool := (b >= 32 && b != 127) || b == 9

structure RequestLine where
  methodStart : Nat
  methodEnd : Nat
  targetStart : Nat
  targetEnd : Nat
  headersStart : Nat
  minor : Nat

/-- Strict request-line envelope. The target's URI grammar is checked separately
by parseTarget. Major versions other than 1 are rejected with 505. -/
def parseRequestLine (bytes : ByteArray) (start stop maxTarget : Nat) : Except Nat RequestLine :=
  if start ≥ stop || stop > bytes.size then .error 400
  else
    let methodEnd := spanEnd bytes stop token start
    if methodEnd == start || methodEnd ≥ stop || bytes[methodEnd]! != 32 then .error 400
    else
      let targetStart := methodEnd + 1
      let targetEnd := spanEnd bytes stop targetOctet targetStart
      if targetEnd == targetStart || targetEnd ≥ stop || bytes[targetEnd]! != 32 then .error 400
      else if targetEnd - targetStart > maxTarget then .error 414
      else if targetEnd + 11 > stop ||
          bytes[targetEnd + 1]! != 72 || bytes[targetEnd + 2]! != 84 ||
          bytes[targetEnd + 3]! != 84 || bytes[targetEnd + 4]! != 80 ||
          bytes[targetEnd + 5]! != 47 || bytes[targetEnd + 7]! != 46 ||
          bytes[targetEnd + 9]! != 13 || bytes[targetEnd + 10]! != 10 then .error 400
      else
        let major := bytes[targetEnd + 6]!
        let minor := bytes[targetEnd + 8]!
        if major < 48 || major > 57 || minor < 48 || minor > 57 then .error 400
        else if major != 49 then .error 505
        else .ok ⟨start, methodEnd, targetStart, targetEnd, targetEnd + 11, minor.toNat - 48⟩

structure FieldLine where
  start : Nat
  colon : Nat
  valueStart : Nat
  valueEnd : Nat
  next : Nat

/-- Strict field-line envelope: nonempty token, colon, field octets, CRLF.
Whitespace belongs to the field value, never to the field name. -/
def parseFieldLine (bytes : ByteArray) (start stop : Nat) : Option FieldLine :=
  if start ≥ stop || stop > bytes.size then none
  else
    let colon := spanEnd bytes stop token start
    if colon == start || colon ≥ stop || bytes[colon]! != 58 then none
    else
      let valueStart := colon + 1
      let valueEnd := spanEnd bytes stop fieldOctet valueStart
      if valueEnd + 2 > stop || bytes[valueEnd]! != 13 || bytes[valueEnd + 1]! != 10 then none
      else some ⟨start, colon, valueStart, valueEnd, valueEnd + 2⟩

end FastHTTP.Protocol
