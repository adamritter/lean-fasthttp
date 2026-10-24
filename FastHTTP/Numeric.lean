import Init

namespace FastHTTP.Protocol

/-- One decimal octet. Arithmetic is on naturals, without machine overflow. -/
@[inline] def decimalStep (limit n : Nat) (b : UInt8) : Option Nat :=
  if 48 ≤ b.toNat ∧ b.toNat ≤ 57 then
    let next := n * 10 + (b.toNat - 48)
    if next ≤ limit then some next else none
  else none

/-- Bounded, terminating decimal parser. The cursor is checked before indexing. -/
def decimalLoop (bytes : ByteArray) (stop limit i n : Nat) : Option Nat :=
  if h : i < stop ∧ i < bytes.size then
    match decimalStep limit n bytes[i] with
    | none => none
    | some next => decimalLoop bytes stop limit (i + 1) next
  else some n
termination_by stop - i

/-- Content-Length is one or more ASCII digits, bounded by the configured limit. -/
def decimal (bytes : ByteArray) (start stop limit : Nat) : Option Nat :=
  if start < stop ∧ stop ≤ bytes.size then decimalLoop bytes stop limit start 0 else none

end FastHTTP.Protocol
