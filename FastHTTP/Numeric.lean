import FastHTTP.Syntax

namespace FastHTTP.Protocol

/-- ASCII hexadecimal value; 16 is the explicit non-HEXDIG sentinel. -/
@[inline] def hexValue (octet : UInt8) : Nat :=
  let b := lower octet
  if b >= 48 && b <= 57 then b.toNat - 48
  else if b >= 97 && b <= 102 then b.toNat - 87 else 16

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

@[inline] def hexadecimalStep (limit n : Nat) (b : UInt8) : Option Nat :=
  if hexValue b < 16 then
    let next := n * 16 + hexValue b
    if next ≤ limit then some next else none
  else none

def hexadecimalLoop (bytes : ByteArray) (stop limit i n : Nat) : Option Nat :=
  if h : i < stop ∧ i < bytes.size then
    match hexadecimalStep limit n bytes[i] with
    | none => none
    | some next => hexadecimalLoop bytes stop limit (i + 1) next
  else some n
termination_by stop - i

def hexadecimal (bytes : ByteArray) (start stop limit : Nat) : Option Nat :=
  if start < stop ∧ stop ≤ bytes.size then hexadecimalLoop bytes stop limit start 0 else none

end FastHTTP.Protocol
