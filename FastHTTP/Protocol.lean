import FastHTTP.Syntax

namespace FastHTTP

/-- Owns the receive buffer: safe to retain across asynchronous work. String
conversion is lazy; routing with `targetIs` does not copy the target bytes. -/
structure Request where
  raw : ByteArray
  methodEnd : Nat
  targetStart : Nat
  targetEnd : Nat
  headersStart : Nat
  headEnd : Nat
  close : Bool
  isHead : Bool
  body : ByteArray := .empty
  rawTrailers : Array (String × ByteArray) := #[]
  methodStart : Nat := 0
  versionMinor : Nat := 1
  pathStart : Option Nat := none
  authoritySpan : Option (Nat × Nat) := none
  schemeEnd : Option Nat := none

def Request.method (r : Request) : String :=
  String.fromUTF8! (r.raw.extract r.methodStart r.methodEnd)
def Request.requestTarget (r : Request) : String :=
  String.fromUTF8! (r.raw.extract r.targetStart r.targetEnd)
def Request.target (r : Request) : String :=
  let start := r.pathStart.getD r.targetStart
  let path := String.fromUTF8! (r.raw.extract start r.targetEnd)
  if r.pathStart.isSome && (start == r.targetEnd || r.raw[start]! == 63) then "/" ++ path else path
def Request.targetIs (r : Request) (target : String) : Bool :=
  let start := r.pathStart.getD r.targetStart
  if r.pathStart.isSome && (start == r.targetEnd || r.raw[start]! == 63) then r.target == target
  else equals r.raw start r.targetEnd target

/-- Text convenience view; rawTrailers preserves every field-value octet, including obs-text. -/
def Request.trailers (r : Request) : Array (String × String) :=
  r.rawTrailers.map fun (name, value) =>
    (name, (String.fromUTF8? value).getD (String.ofList (value.data.toList.map (Char.ofNat ·.toNat))))

/-- First matching header, ASCII case insensitive; trims optional whitespace.
Lookup allocates only when called by the application. -/
def Request.headerBytes? (r : Request) (name : String) : Option ByteArray := Id.run do
  let mut start := r.headersStart
  let mut colon := start
  for i in [start:r.headEnd - 2] do
    let b := r.raw[i]!
    if b == 58 && colon == start then colon := i
    if b == 13 then
      if equals r.raw start colon name true then
        let mut first := colon + 1
        let mut last := i
        while first < last && space r.raw[first]! do first := first + 1
        while last > first && space r.raw[last - 1]! do last := last - 1
        return some (r.raw.extract first last)
      start := i + 2
      colon := start
  return none

def Request.header? (r : Request) (name : String) : Option String :=
  (r.headerBytes? name).bind String.fromUTF8?

/-- Effective authority for routing: absolute-form overrides the received Host. -/
def Request.authority (r : Request) : String :=
  match r.authoritySpan with
  | some (first, last) => String.fromUTF8! (r.raw.extract first last)
  | none => (r.header? "host").getD ""

def Request.scheme? (r : Request) : Option String :=
  r.schemeEnd.map fun last => String.fromUTF8! (r.raw.extract r.targetStart last)

def hasClose (bytes : ByteArray) (start stop : Nat) : Bool := Id.run do
  let mut first := start
  for i in [start:stop + 1] do
    if i == stop || bytes[i]! == 44 then
      let mut a := first
      let mut b := i
      while a < b && space bytes[a]! do a := a + 1
      while b > a && space bytes[b - 1]! do b := b - 1
      if equals bytes a b "close" true then return true
      first := i + 1
  return false

structure Config where
  maxHeaderBytes : Nat := 16384
  maxTargetBytes : Nat := 8192
  maxBodyBytes : Nat := 1024 * 1024
  maxChunkLineBytes : Nat := 1024
  maxTrailerBytes : Nat := 16384
  maxChunks : Nat := 65536

namespace Protocol

inductive Framing where
  | fixed (length : Nat)
  | chunked
  deriving BEq, Repr

/-- Reject conflicting framing even if one header would otherwise take priority. -/
def chooseFraming (length : Option Nat) (chunked : Bool) : Except Nat Framing :=
  match length, chunked with
  | some _, true => .error 400
  | _, true => .ok .chunked
  | some n, false => .ok (.fixed n)
  | none, false => .ok (.fixed 0)

structure ScanState where
  matched : Nat := 0
  count : Nat := 0
  stop : Option Nat := none
  invalid : Bool := false
  deriving BEq, Repr

/-- Absorbing after the first delimiter: following body/pipeline bytes are untouched. -/
@[inline] def scanByte (limit : Nat) (s : ScanState) (b : UInt8) : ScanState :=
  if s.stop.isSome || s.invalid then s
  else if s.count >= limit then { s with invalid := true }
  else
    let matched := if b == 13 then (if s.matched == 2 then 3 else 1)
      else if b == 10 then (if s.matched == 1 then 2 else if s.matched == 3 then 4 else 0)
      else 0
    let count := s.count + 1
    { matched, count, stop := if matched == 4 then some count else none }

def scanFeed (limit : Nat) (s : ScanState) (bytes : ByteArray) : ScanState :=
  bytes.data.foldl (scanByte limit) s

/-- Early exit avoids examining body and pipelined bytes after the delimiter.
The refinement theorem in Proofs equates this loop with scanFeed for every state. -/
def scanLoop (limit : Nat) (bytes : ByteArray) (i : Nat) (s : ScanState) : ScanState :=
  if s.stop.isSome || s.invalid then s
  else if h : i < bytes.size then scanLoop limit bytes (i + 1) (scanByte limit s bytes[i])
  else s
termination_by bytes.size - i

def scanFeedFast (limit : Nat) (s : ScanState) (bytes : ByteArray) : ScanState :=
  scanLoop limit bytes 0 s

/-- Bounded decimal parsing: avoid unbounded Nat growth from hostile headers. -/
def decimal (bytes : ByteArray) (start stop limit : Nat) : Option Nat := Id.run do
  if start == stop then return none
  let mut n := 0
  for i in [start:stop] do
    let b := bytes[i]!
    if b < 48 || b > 57 then return none
    n := n * 10 + b.toNat - 48
    if n > limit then return none
  return some n

structure Head where
  request : Request
  framing : Framing
  expectContinue : Bool

structure HeaderState where
  line : Nat
  colon : Nat
  close : Bool := false
  length : Option Nat := none
  chunked : Bool := false
  host : Bool := false
  expectContinue : Bool := false
  unsupportedTransfer : Bool := false

private def parseField (cfg : Config) (bytes : ByteArray) (i stop minor : Nat)
    (initial : HeaderState) : Except Nat HeaderState := do
  let mut state := initial
  if i + 1 >= stop || bytes[i + 1]! != 10 || state.colon == state.line then throw 400
  let mut first := state.colon + 1
  let mut last := i
  while first < last && space bytes[first]! do first := first + 1
  while last > first && space bytes[last - 1]! do last := last - 1
  if equals bytes state.line state.colon "content-length" true then
    if state.length.isSome then throw 400
    -- Distinguish syntactically invalid lengths from the configured size limit.
    if first == last then throw 400
    for k in [first:last] do
      if bytes[k]! < 48 || bytes[k]! > 57 then throw 400
    match decimal bytes first last cfg.maxBodyBytes with
    | none => throw 413
    | some n => state := { state with length := some n }
  else if equals bytes state.line state.colon "transfer-encoding" true then
    if minor == 0 || state.chunked then throw 400
    let unsupportedTransfer ← transferCodings bytes first last
    state := { state with chunked := true, unsupportedTransfer }
  else if equals bytes state.line state.colon "host" true then
    if state.host || !validAuthority bytes first last then throw 400
    state := { state with host := true }
  else if minor != 0 && equals bytes state.line state.colon "expect" true then
    if state.expectContinue || !equals bytes first last "100-continue" true then throw 417
    state := { state with expectContinue := true }
  else if equals bytes state.line state.colon "connection" true then
    let closing ← connectionOptions bytes first last
    state := { state with close := state.close || closing }
  return { state with line := i + 2, colon := i + 2 }

/-- Tail recursion avoids constructing nested mutable-variable tuples per byte. -/
private def parseHeaders (cfg : Config) (bytes : ByteArray) (headersStart stop minor : Nat) :
    Except Nat HeaderState := loop headersStart { line := headersStart, colon := headersStart }
where
  loop (i : Nat) (state : HeaderState) : Except Nat HeaderState :=
    if i < stop - 2 then
      let b := bytes[i]!
      if b == 13 then
        match parseField cfg bytes i stop minor state with
        | .error code => .error code
        | .ok state => loop (i + 1) state
      else if b == 10 then
        if i + 1 != state.line then .error 400 else loop (i + 1) state
      else if state.colon == state.line then
        if b == 58 then
          if i == state.line then .error 400 else loop (i + 1) { state with colon := i }
        else if !token b then .error 400 else loop (i + 1) state
      else if (b < 32 && b != 9) || b == 127 then .error 400
      else loop (i + 1) state
    else if state.line != stop - 2 || (minor != 0 && !state.host) then .error 400 else .ok state
  termination_by stop - 2 - i

/-- Strict origin-server grammar. Duplicated framing fields and obsolete folding
are rejected; methods are tokens, targets are origin-form or OPTIONS *. -/
def parseHead (cfg : Config) (bytes : ByteArray) (stop : Nat) : Except Nat Head := do
  if stop > bytes.size || stop < 18 || !equals bytes (stop - 4) stop "\r\n\r\n" then throw 400
  let methodStart := if equals bytes 0 2 "\r\n" then 2 else 0
  let mut methodEnd := methodStart
  while methodEnd < stop && bytes[methodEnd]! != 32 do
    if !token bytes[methodEnd]! then throw 400
    methodEnd := methodEnd + 1
  if methodEnd == methodStart then throw 400
  let targetStart := methodEnd + 1
  let mut targetEnd := targetStart
  while targetEnd < stop && bytes[targetEnd]! != 32 do
    let b := bytes[targetEnd]!
    if b < 33 || b > 126 || b == 35 then throw 400
    -- Percent escapes must contain exactly two hex digits (checked below).
    targetEnd := targetEnd + 1
  if targetEnd == targetStart then throw 400
  if targetEnd - targetStart > cfg.maxTargetBytes then throw 414
  if targetEnd + 11 > stop ||
      !equals bytes (targetEnd + 1) (targetEnd + 6) "HTTP/" ||
      bytes[targetEnd + 7]! != 46 || bytes[targetEnd + 9]! != 13 || bytes[targetEnd + 10]! != 10 then
    throw 400
  let major := bytes[targetEnd + 6]!
  let minor := bytes[targetEnd + 8]!
  if major < 48 || major > 57 || minor < 48 || minor > 57 then throw 400
  if major != 49 then throw 505
  let minor := minor.toNat - 48
  let target ← parseTarget bytes targetStart targetEnd
    (equals bytes methodStart methodEnd "OPTIONS") (equals bytes methodStart methodEnd "CONNECT")
  let headersStart := targetEnd + 11
  let fields ← parseHeaders cfg bytes headersStart stop minor
  let framing ← chooseFraming fields.length fields.chunked
  if fields.unsupportedTransfer then throw 501
  if equals bytes methodStart methodEnd "CONNECT" then throw 501
  let request : Request := {
    raw := bytes, methodStart, methodEnd, targetStart, targetEnd, headersStart, headEnd := stop
    close := fields.close || minor == 0, isHead := equals bytes methodStart methodEnd "HEAD"
    versionMinor := minor, pathStart := if target.authority.isSome then some target.pathStart else none
    authoritySpan := target.authority, schemeEnd := target.schemeEnd }
  return ⟨request, framing, fields.expectContinue⟩

/-- Used for both fixed bodies and chunk data. Slice boundaries are proved in Proofs. -/
def takeCount (remaining available : Nat) : Nat := min remaining available

def takeBody (bytes : ByteArray) (start remaining : Nat) : ByteArray × Nat :=
  let stop := start + takeCount remaining (bytes.size - start)
  (bytes.extract start stop, stop)

inductive BodyPhase where
  | fixed (remaining : Nat)
  | sizeLine
  | data (remaining : Nat)
  | dataCR
  | dataLF
  | trailers
  deriving Repr

structure BodyState where
  phase : BodyPhase
  body : ByteArray := .empty
  line : ByteArray := .empty
  sawCR : Bool := false
  trailerBytes : Nat := 0
  trailers : Array (String × ByteArray) := #[]
  chunks : Nat := 0

inductive BodyResult where
  | need (state : BodyState)
  | done (body : ByteArray) (trailers : Array (String × ByteArray)) (stop : Nat)
  | error (status : Nat)

/-- Chunk extensions: token names and token/quoted-string values, with OWS. -/
def chunkSize (line : ByteArray) (limit : Nat) : Except Nat Nat := do
  let mut i := 0
  let mut n := 0
  while i < line.size do
    let b := lower line[i]!
    let digit := if b >= 48 && b <= 57 then b.toNat - 48
      else if b >= 97 && b <= 102 then b.toNat - 87 else 16
    if digit == 16 then break
    n := n * 16 + digit
    if n > limit then throw 413
    i := i + 1
  if i == 0 then throw 400
  while i < line.size do
    while i < line.size && space line[i]! do i := i + 1
    if i == line.size || line[i]! != 59 then throw 400
    i := i + 1
    while i < line.size && space line[i]! do i := i + 1
    let start := i
    while i < line.size && token line[i]! do i := i + 1
    if i == start then throw 400
    let nameEnd := i
    while i < line.size && space line[i]! do i := i + 1
    if i == line.size && i != nameEnd then throw 400
    if i < line.size && line[i]! == 61 then
      i := i + 1
      while i < line.size && space line[i]! do i := i + 1
      if i < line.size && line[i]! == 34 then
        i := i + 1
        let mut closed := false
        while i < line.size do
          let b := line[i]!
          i := i + 1
          if b == 34 then
            closed := true
            break
          if b == 92 then
            if i == line.size then throw 400
            let b := line[i]!
            if (b < 32 && b != 9) || b == 127 then throw 400
            i := i + 1
          else if (b < 32 && b != 9) || b == 127 then throw 400
        if !closed then throw 400
      else
        let start := i
        while i < line.size && token line[i]! do i := i + 1
        if i == start then throw 400
  return n

def trailer (line : ByteArray) : Except Nat (String × ByteArray) := do
  let mut i := 0
  while i < line.size && token line[i]! do i := i + 1
  if i == 0 || i == line.size || line[i]! != 58 then throw 400
  -- Trailer fields never overwrite request headers or framing information.
  for name in ["content-length", "transfer-encoding", "host", "connection", "trailer",
      "authorization", "proxy-authorization", "content-type", "content-encoding", "expect", "upgrade"] do
    if equals line 0 i name true then throw 400
  let name := String.fromUTF8! (line.extract 0 i)
  let mut first := i + 1
  let mut last := line.size
  for j in [first:last] do
    let b := line[j]!
    if (b < 32 && b != 9) || b == 127 then throw 400
  while first < last && space line[first]! do first := first + 1
  while last > first && space line[last - 1]! do last := last - 1
  return (name, line.extract first last)

/-- Pure, bounded buffered-body decoder. It stops exactly at the message boundary. -/
def decodeBody (cfg : Config) (bytes : ByteArray) (start : Nat) (initial : BodyState) : BodyResult := Id.run do
  let mut s := initial
  let mut i := start
  repeat
    match s.phase with
    | .fixed remaining | .data remaining =>
      let (piece, stop) := takeBody bytes i remaining
      let body := if s.body.isEmpty then piece else s.body ++ piece
      let left := remaining - (stop - i)
      i := stop
      match s.phase with
      | .fixed _ =>
        if left == 0 then return .done body s.trailers i
        return .need { s with body, phase := .fixed left }
      | _ =>
        s := { s with body, phase := if left == 0 then .dataCR else .data left }
        if left != 0 then return .need s
    | .dataCR =>
      if i == bytes.size then return .need s
      if bytes[i]! != 13 then return .error 400
      i := i + 1
      s := { s with phase := .dataLF }
    | .dataLF =>
      if i == bytes.size then return .need s
      if bytes[i]! != 10 then return .error 400
      i := i + 1
      s := { s with phase := .sizeLine }
    | .sizeLine | .trailers =>
      if i == bytes.size then return .need s
      let b := bytes[i]!
      i := i + 1
      if let .trailers := s.phase then
        s := { s with trailerBytes := s.trailerBytes + 1 }
        if s.trailerBytes > cfg.maxTrailerBytes then return .error 431
      if s.sawCR then
        if b != 10 then return .error 400
        match s.phase with
        | .sizeLine =>
          match chunkSize s.line (cfg.maxBodyBytes - s.body.size) with
          | .error status => return .error status
          | .ok n =>
            if n != 0 && s.chunks >= cfg.maxChunks then return .error 413
            s := { s with
              phase := if n == 0 then .trailers else .data n
              line := .empty
              sawCR := false
              chunks := s.chunks + (if n == 0 then 0 else 1) }
        | _ =>
          if s.line.isEmpty then return .done s.body s.trailers i
          match trailer s.line with
          | .error status => return .error status
          | .ok field =>
            s := { s with
              line := .empty
              sawCR := false
              trailers := s.trailers.push field }
      else if b == 13 then s := { s with sawCR := true }
      else if b == 10 then return .error 400
      else
        if s.line.size >= cfg.maxChunkLineBytes then return .error 431
        s := { s with line := s.line.push b }
  return .error 400

inductive State where
  | head (pending : ByteArray := .empty) (scan : ScanState := {})
  | body (request : Request) (decoder : BodyState) (pending : ByteArray := .empty) (start : Nat := 0)

inductive Step where
  | need (state : State)
  | «continue» (state : State)
  | request (request : Request) (rest : ByteArray)
  | reject (status : Nat)

def bodyStep (cfg : Config) (request : Request) (decoder : BodyState)
    (bytes : ByteArray) (start : Nat) : Step :=
  match decodeBody cfg bytes start decoder with
  | .need next => .need (.body request next)
  | .error status => .reject status
  | .done body trailers stop =>
    .request { request with body, rawTrailers := trailers } (bytes.extract stop bytes.size)

def headLimitStatus (cfg : Config) (bytes : ByteArray) : Nat := Id.run do
  let mut i := if equals bytes 0 2 "\r\n" then 2 else 0
  while i < bytes.size && token bytes[i]! do i := i + 1
  if i == bytes.size || bytes[i]! != 32 then return 431
  let first := i + 1
  i := first
  while i < bytes.size && bytes[i]! > 32 && bytes[i]! < 127 do i := i + 1
  return if i - first > cfg.maxTargetBytes then 414 else 431

/-- No socket, promise, task, or H1 dependency. One input produces one action.
The driver resumes the returned continuation only after sending the response. -/
def feed (cfg : Config) (state : State) (input : ByteArray) : Step :=
  match state with
  | .body request decoder pending start =>
    bodyStep cfg request decoder (if pending.isEmpty then input else pending ++ input) start
  | .head pending scanner => Id.run do
    let scanner := scanFeedFast cfg.maxHeaderBytes scanner input
    let bytes := if pending.isEmpty then input else pending ++ input
    if scanner.invalid then return .reject (headLimitStatus cfg bytes)
    match scanner.stop with
    | none => return .need (.head bytes scanner)
    | some stop =>
      match parseHead cfg bytes stop with
      | .error status => return .reject status
      | .ok head =>
        if head.framing == .fixed 0 then
          return .request head.request (bytes.extract stop bytes.size)
        let decoder : BodyState := { phase := match head.framing with
          | .fixed n => .fixed n
          | .chunked => .sizeLine }
        if head.expectContinue && head.framing != .fixed 0 then
          return .«continue» (.body head.request decoder bytes stop)
        return bodyStep cfg head.request decoder bytes stop

end Protocol
end FastHTTP
