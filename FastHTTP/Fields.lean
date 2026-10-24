import FastHTTP.Authority

namespace FastHTTP
open Protocol

/-- OWS plus ignored empty comma-list members (RFC 9110, 5.6.1). -/
def listSpace (b : UInt8) : Bool := space b || b == 44

/-- Read one token followed by OWS and a comma or the bounded end. -/
def connectionToken (bytes : ByteArray) (start stop : Nat) : Except Nat (Bool × Nat) :=
  let nameEnd := spanEnd bytes stop token start
  let last := spanEnd bytes stop space nameEnd
  if nameEnd == start || (last < stop && bytes[last]! != 44) then .error 400
  else .ok (equals bytes start nameEnd "close" true, last)

/-- Total comma-list fold. Empty members are ignored; closing is an OR over the
case-insensitive token names, including fields received on previous lines. -/
def connectionList (bytes : ByteArray) (start stop : Nat) (closing : Bool) : Except Nat Bool :=
  let first := spanEnd bytes stop listSpace start
  if first ≥ stop then .ok closing
  else match connectionToken bytes first stop with
    | .error status => .error status
    | .ok (close, last) =>
      if last ≥ stop then .ok (closing || close)
      else if last < start then .error 400
      else connectionList bytes (last + 1) stop (closing || close)
termination_by stop - start

def connectionOptions (bytes : ByteArray) (start stop : Nat) : Except Nat Bool :=
  if start ≤ stop && stop ≤ bytes.size then connectionList bytes start stop false else .error 400

/-- RFC transfer-parameter: ';' OWS token BWS '=' BWS (token / quoted-string).
The leading OWS is consumed by transferParameters. Every success advances. -/
def transferParameter (bytes : ByteArray) (start stop : Nat) : Option Nat :=
  if start ≥ stop || bytes[start]! != 59 then none
  else
    let key := spanEnd bytes stop space (start + 1)
    let nameEnd := spanEnd bytes stop token key
    let eq := spanEnd bytes stop space nameEnd
    if nameEnd == key || eq ≥ stop || bytes[eq]! != 61 then none
    else
      let value := spanEnd bytes stop space (eq + 1)
      if value < stop && bytes[value]! == 34 then quotedEnd bytes value stop
      else
        let last := spanEnd bytes stop token value
        if last == value then none else some last

/-- Parameters end only at a comma or the bounded field end. Chunked cannot have
parameters; extension codings are syntax-checked before the unsupported policy. -/
def transferParameters (bytes : ByteArray) (start stop : Nat) (chunked : Bool) : Option Nat :=
  if start ≥ stop then some start
  else
    let first := spanEnd bytes stop space start
    if first ≥ stop || bytes[first]! == 44 then some first
    else if chunked then none
    else match transferParameter bytes first stop with
      | none => none
      | some last =>
        if last ≤ start then none else transferParameters bytes last stop chunked
termination_by stop - start

def transferCoding (bytes : ByteArray) (start stop : Nat) : Except Nat (Bool × Nat) :=
  let nameEnd := spanEnd bytes stop token start
  if nameEnd == start then .error 400
  else
    let chunked := equals bytes start nameEnd "chunked" true
    match transferParameters bytes nameEnd stop chunked with
    | none => .error 400
    | some last => .ok (chunked, last)

/-- A previous chunked coding forbids any following nonempty list member. Both
within and between field lines, chunked is unique, final, and parameter-free. -/
def transferList (bytes : ByteArray) (start stop : Nat) (chunked unsupported : Bool) :
    Except Nat (Bool × Bool) :=
  let first := spanEnd bytes stop listSpace start
  if first ≥ stop then .ok (chunked, unsupported)
  else if chunked then .error 400
  else match transferCoding bytes first stop with
    | .error status => .error status
    | .ok (nextChunked, last) =>
      if last ≥ stop then .ok (nextChunked, unsupported || !nextChunked)
      else if last < start then .error 400
      else transferList bytes (last + 1) stop nextChunked (unsupported || !nextChunked)
termination_by stop - start

def transferCodings (bytes : ByteArray) (start stop : Nat) (previousChunked := false) :
    Except Nat (Bool × Bool) :=
  if start ≤ stop && stop ≤ bytes.size then transferList bytes start stop previousChunked false
  else .error 400

end FastHTTP
