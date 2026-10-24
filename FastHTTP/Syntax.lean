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

/-- Validate a bounded URI component, preserving percent-encoded octets verbatim. -/
def uriComponent (bytes : ByteArray) (start stop : Nat) (allowed : UInt8 → Bool) : Bool := Id.run do
  if start > stop || stop > bytes.size then return false
  let mut i := start
  while i < stop do
    if bytes[i]! == 37 then
      if i + 2 >= stop || !hexDigit bytes[i + 1]! || !hexDigit bytes[i + 2]! then return false
      i := i + 3
    else
      if !allowed bytes[i]! then return false
      i := i + 1
  return true

def validPathQuery (bytes : ByteArray) (start stop : Nat) : Bool :=
  uriComponent bytes start stop fun b =>
    unreserved b || subDelimiter b || b == 58 || b == 64 || b == 47 || b == 63

private def validIPv4 (s : String) : Bool :=
  let parts := s.splitOn "."
  parts.length == 4 && parts.all fun p =>
    !p.isEmpty && p.utf8ByteSize <= 3 &&
    (p.utf8ByteSize == 1 || !p.startsWith "0") &&
    p.toUTF8.data.all (fun b => b >= 48 && b <= 57) &&
    (p.toNat?.isSome && p.toNat! <= 255)

private def ipv6Groups (s : String) (ipv4 : Bool) : Option Nat := do
  if s.isEmpty then return 0
  let parts := s.splitOn ":"
  let mut n := 0
  for i in [:parts.length] do
    let p := parts[i]!
    if p.isEmpty then failure
    if p.contains '.' then
      if !ipv4 || i + 1 != parts.length || !validIPv4 p then failure
      n := n + 2
    else
      if p.utf8ByteSize > 4 || !p.toUTF8.data.all hexDigit then failure
      n := n + 1
  return n

/-- RFC 3986 IPv6address, including a final IPv4 ls32 and a single :: compression. -/
def validIPv6 (s : String) : Bool :=
  match s.splitOn "::" with
  | [whole] => ipv6Groups whole true == some 8
  | [left, right] => match ipv6Groups left false, ipv6Groups right true with
    | some a, some b => a + b < 8
    | _, _ => false
  | _ => false

private def validIPLiteral (bytes : ByteArray) (start stop : Nat) : Bool := Id.run do
  if start == stop then return false
  if lower bytes[start]! != 118 then
    return validIPv6 (String.fromUTF8! (bytes.extract start stop))
  let mut i := start + 1
  while i < stop && hexDigit bytes[i]! do i := i + 1
  if i == start + 1 || i >= stop || bytes[i]! != 46 then return false
  i := i + 1
  if i == stop then return false
  for j in [i:stop] do
    let b := bytes[j]!
    if !(unreserved b || subDelimiter b || b == 58) then return false
  return true

/-- Host field grammar: uri-host [ ':' port ]. Empty reg-name and empty port are
syntactically permitted by RFC 3986. CONNECT requires a nonempty host and port. -/
def validAuthority (bytes : ByteArray) (start stop : Nat) (connect := false) : Bool := Id.run do
  if start > stop || stop > bytes.size then return false
  let mut i := start
  if i < stop && bytes[i]! == 91 then
    i := i + 1
    while i < stop && bytes[i]! != 93 do i := i + 1
    if i == stop || !validIPLiteral bytes (start + 1) i then return false
    i := i + 1
  else
    while i < stop && bytes[i]! != 58 do
      let b := bytes[i]!
      if b == 37 then
        if i + 2 >= stop || !hexDigit bytes[i + 1]! || !hexDigit bytes[i + 2]! then return false
        i := i + 3
      else
        if !(unreserved b || subDelimiter b) then return false
        i := i + 1
    if connect && i == start then return false
  if i == stop then return !connect
  if bytes[i]! != 58 then return false
  i := i + 1
  if connect && i == stop then return false
  for j in [i:stop] do
    if bytes[j]! < 48 || bytes[j]! > 57 then return false
  return true

structure TargetInfo where
  pathStart : Nat
  authority : Option (Nat × Nat) := none
  schemeEnd : Option Nat := none
  unsupportedScheme : Bool := false

/-- Validate the request-target without changing the octets used for routing.
Absolute HTTP(S) URIs use their own authority, never the received Host field. -/
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
  let mut colon := start
  while colon < stop && bytes[colon]! != 58 do colon := colon + 1
  if colon == start || colon == stop then throw 400
  let alpha (b : UInt8) := (lower b >= 97 && lower b <= 122)
  if !alpha bytes[start]! then throw 400
  for i in [start + 1:colon] do
    let b := bytes[i]!
    if !(alpha b || (b >= 48 && b <= 57) || b == 43 || b == 45 || b == 46) then throw 400
  let http := equals bytes start colon "http" true || equals bytes start colon "https" true
  let first := colon + 1
  if first + 2 > stop || bytes[first]! != 47 || bytes[first + 1]! != 47 then
    if http || !validPathQuery bytes first stop then throw 400
    return { pathStart := first, schemeEnd := some colon, unsupportedScheme := true }
  let auth := first + 2
  let mut path := auth
  while path < stop && bytes[path]! != 47 && bytes[path]! != 63 do path := path + 1
  let mut host := auth
  for i in [auth:path] do
    if bytes[i]! == 64 then host := i + 1
  if host != auth then
    if http || !uriComponent bytes auth (host - 1) (fun b => unreserved b || subDelimiter b || b == 58) then
      throw 400
  if http && (path == host || bytes[host]! == 58) then throw 400
  if !validAuthority bytes host path || !validPathQuery bytes path stop then throw 400
  return {
    pathStart := path
    authority := some (host, path)
    schemeEnd := some colon
    unsupportedScheme := !http }

/-- A Connection field is a comma-list of tokens. Empty list members are ignored
as required for recipients by RFC 9110 section 5.6.1. -/
def connectionOptions (bytes : ByteArray) (start stop : Nat) : Except Nat Bool := do
  let mut first := start
  let mut closing := false
  for i in [start:stop + 1] do
    if i == stop || bytes[i]! == 44 then
      let mut a := first
      let mut b := i
      while a < b && space bytes[a]! do a := a + 1
      while b > a && space bytes[b - 1]! do b := b - 1
      for j in [a:b] do
        if !token bytes[j]! then throw 400
      closing := closing || equals bytes a b "close" true
      first := i + 1
  return closing

/-- Parse a Transfer-Encoding list. The only implemented coding is chunked;
syntactically valid preceding extension codings are reported as unsupported.
Chunked must occur exactly once, last, and without parameters. -/
def transferCodings (bytes : ByteArray) (start stop : Nat) (previousChunked := false) :
    Except Nat (Bool × Bool) := do
  let mut i := start
  let mut chunked := previousChunked
  let mut unsupported := false
  while i < stop do
    while i < stop && (space bytes[i]! || bytes[i]! == 44) do i := i + 1
    if i == stop then break
    if chunked then throw 400
    let first := i
    while i < stop && token bytes[i]! do i := i + 1
    if i == first then throw 400
    chunked := equals bytes first i "chunked" true
    unsupported := unsupported || !chunked
    while i < stop do
      while i < stop && space bytes[i]! do i := i + 1
      if i == stop || bytes[i]! == 44 then break
      if bytes[i]! != 59 || chunked then throw 400
      i := i + 1
      while i < stop && space bytes[i]! do i := i + 1
      let key := i
      while i < stop && token bytes[i]! do i := i + 1
      if i == key then throw 400
      while i < stop && space bytes[i]! do i := i + 1
      if i == stop || bytes[i]! != 61 then throw 400
      i := i + 1
      while i < stop && space bytes[i]! do i := i + 1
      if i < stop && bytes[i]! == 34 then
        i := i + 1
        let mut closed := false
        while i < stop do
          let b := bytes[i]!
          i := i + 1
          if b == 34 then
            closed := true
            break
          if b == 92 then
            if i == stop then throw 400
            let escaped := bytes[i]!
            if (escaped < 32 && escaped != 9) || escaped == 127 then throw 400
            i := i + 1
          else if (b < 32 && b != 9) || b == 127 then throw 400
        if !closed then throw 400
      else
        let value := i
        while i < stop && token bytes[i]! do i := i + 1
        if i == value then throw 400
  return (chunked, unsupported)

end FastHTTP
