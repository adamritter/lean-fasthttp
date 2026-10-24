import Init

/-! Byte-oriented RFC 3986 syntax. No Unicode normalization, decoding of percent
escapes, DNS lookup, or authority-dependent routing is performed here. -/
namespace FastHTTP

def lower (b : UInt8) : UInt8 := if b >= 65 && b <= 90 then b + 32 else b

def equals (bytes : ByteArray) (start stop : Nat) (text : String)
    (ignoreCase := false) : Bool :=
  stop - start == text.utf8ByteSize && loop 0
where
  loop (i : Nat) : Bool :=
    if h : i < text.utf8ByteSize then
      let a := bytes[start + i]!
      let b := text.getUTF8Byte ⟨i⟩ h
      (if ignoreCase then lower a == lower b else a == b) && loop (i + 1)
    else true
  termination_by text.utf8ByteSize - i

def token (b : UInt8) : Bool :=
  (b >= 65 && b <= 90) || (b >= 97 && b <= 122) || (b >= 48 && b <= 57) ||
  b == 33 || b == 35 || b == 36 || b == 37 || b == 38 || b == 39 ||
  b == 42 || b == 43 || b == 45 || b == 46 || b == 94 || b == 95 ||
  b == 96 || b == 124 || b == 126

def space (b : UInt8) : Bool := b == 32 || b == 9


def hexDigit (b : UInt8) : Bool :=
  (b >= 48 && b <= 57) || (lower b >= 97 && lower b <= 102)

def unreserved (b : UInt8) : Bool :=
  (b >= 65 && b <= 90) || (b >= 97 && b <= 122) || (b >= 48 && b <= 57) ||
  b == 45 || b == 46 || b == 95 || b == 126

def subDelimiter (b : UInt8) : Bool :=
  b == 33 || b == 36 || b == 38 || b == 39 || b == 40 || b == 41 ||
  b == 42 || b == 43 || b == 44 || b == 59 || b == 61

/-- Terminating, allocation-free traversal of URI atoms. -/
def uriLoop (bytes : ByteArray) (stop : Nat) (allowed : UInt8 → Bool) (i : Nat) : Bool :=
  if i < stop then
    if bytes[i]! == 37 then
      if i + 2 < stop && hexDigit bytes[i + 1]! && hexDigit bytes[i + 2]! then
        uriLoop bytes stop allowed (i + 3)
      else false
    else allowed bytes[i]! && uriLoop bytes stop allowed (i + 1)
  else true
termination_by stop - i

/-- Validate a bounded URI component, preserving percent-encoded octets verbatim. -/
def uriComponent (bytes : ByteArray) (start stop : Nat) (allowed : UInt8 → Bool) : Bool :=
  start ≤ stop && stop ≤ bytes.size && uriLoop bytes stop allowed start

def validPathQuery (bytes : ByteArray) (start stop : Nat) : Bool :=
  uriComponent bytes start stop fun b =>
    unreserved b || subDelimiter b || b == 58 || b == 64 || b == 47 || b == 63

/-- RFC 3986 dec-octet: the five ASCII alternatives exclude leading zeros
and values above 255 without integer conversion or overflow. -/
def validDecOctet (xs : List UInt8) : Bool :=
  let digit (b : UInt8) := b >= 48 && b <= 57
  match xs with
  | [a] => digit a
  | [a, b] => a >= 49 && a <= 57 && digit b
  | [a, b, c] =>
    (a == 49 && digit b && digit c) ||
    (a == 50 && b >= 48 && b <= 52 && digit c) ||
    (a == 50 && b == 53 && c >= 48 && c <= 53)
  | _ => false

def validIPv4 (s : String) : Bool :=
  let parts := s.splitOn "."
  parts.length == 4 && parts.all fun p => validDecOctet p.toUTF8.data.toList

def validH16 (s : String) : Bool :=
  s.utf8ByteSize > 0 && s.utf8ByteSize ≤ 4 && s.toUTF8.data.all hexDigit

/-- Structural traversal is linear in the number of groups, including malformed
long inputs; the old indexed List traversal was quadratic. -/
def ipv6Parts (parts : List String) (ipv4 : Bool) : Option Nat :=
  match parts with
  | [] => some 0
  | p :: rest =>
    if p.contains '.' then
      if ipv4 && rest.isEmpty && validIPv4 p then some 2 else none
    else if validH16 p then (ipv6Parts rest ipv4).map (· + 1) else none

def ipv6Groups (s : String) (ipv4 : Bool) : Option Nat :=
  if s.isEmpty then some 0 else ipv6Parts (s.splitOn ":") ipv4

/-- RFC 3986 IPv6address, including a final IPv4 ls32 and a single :: compression. -/
def validIPv6 (s : String) : Bool :=
  match s.splitOn "::" with
  | [whole] => ipv6Groups whole true == some 8
  | [left, right] => match ipv6Groups left false, ipv6Groups right true with
    | some a, some b => a + b < 8
    | _, _ => false
  | _ => false

/-- Reject malformed UTF-8 without panic before interpreting an IPv6 literal. -/
def utf8IPv6 (bytes : ByteArray) : Bool :=
  match String.fromUTF8? bytes with
  | none => false
  | some text => validIPv6 text

end FastHTTP
