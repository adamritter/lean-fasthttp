import FastHTTP.Lexical

namespace FastHTTP
open Protocol

def decimalOctet (b : UInt8) : Bool := b >= 48 && b <= 57

def futureOctet (b : UInt8) : Bool := unreserved b || subDelimiter b || b == 58

/-- RFC 3986 IPvFuture, with a nonempty hexadecimal version and address. -/
def validIPvFuture (bytes : ByteArray) (start stop : Nat) : Bool :=
  if start < stop && stop ≤ bytes.size && (bytes[start]! == 118 || bytes[start]! == 86) then
    let dot := spanEnd bytes stop hexDigit (start + 1)
    start + 1 < dot && dot < stop && bytes[dot]! == 46 && dot + 1 < stop &&
      spanEnd bytes stop futureOctet (dot + 1) == stop
  else false

/-- A bracket interior cannot contain a closing bracket. This explicit lexical
boundary also makes malformed UTF-8 and arbitrary input intervals total. -/
def validIPLiteral (bytes : ByteArray) (start stop : Nat) : Bool :=
  start < stop && stop ≤ bytes.size &&
    spanEnd bytes stop (fun b => b != 93) start == stop &&
    (utf8IPv6 (bytes.extract start stop) || validIPvFuture bytes start stop)

/-- RFC port is zero or more decimal digits; CONNECT requires at least one. -/
def validPort (bytes : ByteArray) (start stop : Nat) (required : Bool) : Bool :=
  if start == stop then !required
  else start < stop && bytes[start]! == 58 && (!required || start + 1 < stop) &&
    spanEnd bytes stop decimalOctet (start + 1) == stop

/-- Host field grammar: uri-host [ ':' port ]. Empty reg-name and empty port are
permitted by RFC 3986. CONNECT requires a nonempty host and port. -/
def validAuthority (bytes : ByteArray) (start stop : Nat) (connect := false) : Bool :=
  if start ≤ stop && stop ≤ bytes.size then
    if start < stop && bytes[start]! == 91 then
      let close := spanEnd bytes stop (fun b => b != 93) (start + 1)
      close < stop && validIPLiteral bytes (start + 1) close &&
        validPort bytes (close + 1) stop connect
    else
      let colon := spanEnd bytes stop (fun b => b != 58) start
      (!connect || start < colon) &&
        uriComponent bytes start colon (fun b => unreserved b || subDelimiter b) &&
        validPort bytes colon stop connect
  else false

structure TargetInfo where
  pathStart : Nat
  authority : Option (Nat × Nat) := none
  schemeEnd : Option Nat := none
  unsupportedScheme : Bool := false

def alphaOctet (b : UInt8) : Bool :=
  (b >= 65 && b <= 90) || (b >= 97 && b <= 122)

def schemeOctet (b : UInt8) : Bool :=
  alphaOctet b || decimalOctet b || b == 43 || b == 45 || b == 46

/-- Interpret an already identified hierarchical absolute-URI suffix. -/
def parseHierarchicalTarget (bytes : ByteArray) (first stop : Nat) (http : Bool) (colon : Nat) :
    Except Nat TargetInfo :=
  let auth := first + 2
  let path := spanEnd bytes stop (fun b => b != 47 && b != 63) auth
  let userEnd := spanEnd bytes path (fun b => b != 64) auth
  let host := if userEnd < path then userEnd + 1 else auth
  if (host != auth && (http || !uriComponent bytes auth (host - 1) futureOctet)) ||
      (http && (path == host || bytes[host]! == 58)) ||
      !validAuthority bytes host path || !validPathQuery bytes path stop then .error 400
  else .ok (TargetInfo.mk path (some (host, path)) (some colon) (!http))

/-- Interpret the scheme and hierarchy of an absolute request-target. -/
def parseAbsoluteTarget (bytes : ByteArray) (start stop : Nat) : Except Nat TargetInfo := do
  let colon := spanEnd bytes stop (fun b => b != 58) start
  if colon == start || colon == stop then throw 400
  if !alphaOctet bytes[start]! ||
      spanEnd bytes colon schemeOctet (start + 1) != colon then throw 400
  let http := equals bytes start colon "http" true || equals bytes start colon "https" true
  let first := colon + 1
  if first + 2 > stop || bytes[first]! != 47 || bytes[first + 1]! != 47 then
    if http || !validPathQuery bytes first stop then throw 400
    return { pathStart := first, schemeEnd := some colon, unsupportedScheme := true }
  parseHierarchicalTarget bytes first stop http colon

/-- Validate all four request-target forms without changing routing octets.
Unsupported absolute schemes are syntactically validated before the 501 policy. -/
def parseTarget (bytes : ByteArray) (start stop : Nat) (isOptions isConnect : Bool) :
    Except Nat TargetInfo := do
  if start >= stop || stop > bytes.size then throw 400
  if isConnect then
    if !validAuthority bytes start stop true then throw 400
    return { pathStart := start }
  if equals bytes start stop "*" then
    if !isOptions then throw 400
    return { pathStart := start }
  if bytes[start]! == 47 then
    if !validPathQuery bytes start stop then throw 400
    return { pathStart := start }
  parseAbsoluteTarget bytes start stop

end FastHTTP
