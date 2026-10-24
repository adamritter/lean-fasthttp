import FastHTTP.Lexical

namespace FastHTTP

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
        match Protocol.quotedEnd bytes i stop with
        | none => throw 400
        | some last => i := last
      else
        let value := i
        while i < stop && token bytes[i]! do i := i + 1
        if i == value then throw 400
  return (chunked, unsupported)

end FastHTTP
