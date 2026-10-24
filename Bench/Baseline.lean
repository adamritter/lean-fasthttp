import Std.Internal.UV.TCP

/-! Experimental bodyless HTTP/1.1 GET server on Lean's built-in libuv binding.
The handler runs on a Lean worker. Socket operations and deferred responses use
continuations; no worker blocks waiting for a client. This is not full HTTP/1.1:
request bodies, other methods, upgrades, TLS and timeouts are not implemented.
-/
namespace BaselineHTTP

private def lower (b : UInt8) : UInt8 := if b >= 65 && b <= 90 then b + 32 else b

private def equals (bytes : ByteArray) (start stop : Nat) (text : String)
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

private def token (b : UInt8) : Bool :=
  (b >= 65 && b <= 90) || (b >= 97 && b <= 122) || (b >= 48 && b <= 57) ||
  b == 33 || b == 35 || b == 36 || b == 37 || b == 38 || b == 39 ||
  b == 42 || b == 43 || b == 45 || b == 46 || b == 94 || b == 95 ||
  b == 96 || b == 124 || b == 126

private def space (b : UInt8) : Bool := b == 32 || b == 9

/-- Owns the receive buffer: safe to retain across asynchronous work. String
conversion is lazy; routing with `targetIs` does not copy the target bytes. -/
structure Request where
  private raw : ByteArray
  private targetStart : Nat
  private targetEnd : Nat
  private headersStart : Nat
  private headEnd : Nat
  close : Bool

def Request.method (_ : Request) : String := "GET"
def Request.target (r : Request) : String :=
  String.fromUTF8! (r.raw.extract r.targetStart r.targetEnd)
def Request.targetIs (r : Request) (target : String) : Bool :=
  equals r.raw r.targetStart r.targetEnd target

/-- First matching header, ASCII case insensitive; trims optional whitespace.
Lookup allocates only when called by the application. -/
def Request.header? (r : Request) (name : String) : Option String := Id.run do
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
        return String.fromUTF8? (r.raw.extract first last)
      start := i + 2
      colon := start
  return none

private def hasClose (bytes : ByteArray) (start stop : Nat) : Bool := Id.run do
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

/-- Strict framing for the supported subset. Reject ambiguous body framing
before calling the handler, so body bytes cannot become another request. -/
private def parse (bytes : ByteArray) (start stop : Nat) : Option Request := Id.run do
  if stop - start < 18 || !equals bytes start (start + 4) "GET " then return none
  let targetStart := start + 4
  let mut targetEnd := targetStart
  while targetEnd < stop && bytes[targetEnd]! != 32 do
    if bytes[targetEnd]! < 33 || bytes[targetEnd]! > 126 then return none
    targetEnd := targetEnd + 1
  if targetEnd == targetStart || bytes[targetStart]! != 47 then return none
  if targetEnd + 11 > stop ||
      !equals bytes (targetEnd + 1) (targetEnd + 11) "HTTP/1.1\r\n" then return none
  let headersStart := targetEnd + 11
  let mut line := headersStart
  let mut colon := line
  let mut close := false
  let mut contentLength := false
  for i in [headersStart:stop - 2] do
    let b := bytes[i]!
    if b == 13 then
      if i + 1 >= stop || bytes[i + 1]! != 10 || colon == line then return none
      let mut first := colon + 1
      let mut last := i
      while first < last && space bytes[first]! do first := first + 1
      while last > first && space bytes[last - 1]! do last := last - 1
      if equals bytes line colon "content-length" true then
        if contentLength || first == last then return none
        for j in [first:last] do
          if bytes[j]! != 48 then return none
        contentLength := true
      if equals bytes line colon "transfer-encoding" true ||
          equals bytes line colon "expect" true ||
          equals bytes line colon "upgrade" true then return none
      if equals bytes line colon "connection" true && hasClose bytes first last then
        close := true
      line := i + 2
      colon := line
    else if b == 10 then
      if i + 1 != line then return none
    else if colon == line then
      if b == 58 then
        if i == line then return none
        colon := i
      else if !token b then return none
    else if (b < 32 && b != 9) || b == 127 then return none
  if line != stop - 2 then return none
  return some ⟨bytes, targetStart, targetEnd, headersStart, stop, close⟩

/-- Prepared, immutable wire response. Construct once to reuse across requests.
Both connection modes include the same body and an exact Content-Length. -/
structure Response where
  private keepAlive : Array ByteArray
  private closing : Array ByteArray

def Response.create (body : ByteArray) (status : Nat := 200) (reason := "OK")
    (contentType := "application/octet-stream") : Except String Response := do
  if status < 200 || status > 599 || status == 204 || status == 205 || status == 304 then
    throw "unsupported response status (requires a normal response body)"
  if reason.isEmpty || !(reason.toUTF8.data.all fun b => b >= 32 && b < 127) ||
      contentType.isEmpty || !(contentType.toUTF8.data.all fun b => b >= 32 && b < 127) then
    throw "invalid response reason or content type"
  let responseHead := s!"HTTP/1.1 {status} {reason}\r\nContent-Length: {body.size}\r\nContent-Type: {contentType}\r\nConnection: "
  return ⟨#[(responseHead ++ "keep-alive\r\n\r\n").toUTF8 ++ body],
    #[(responseHead ++ "close\r\n\r\n").toUTF8 ++ body]⟩

/-- The common path allocates no application promise. Deferred replies suspend
this connection until completion, preserving pipeline order and backpressure. -/
inductive Reply where
  | ready (response : Response)
  | deferred (response : IO.Promise (Except IO.Error Response))

/-- Return promptly; use `deferred` for waiting work, not `IO.wait` or blocking I/O. -/
abbrev Handler := Request → IO Reply

private abbrev Socket := Std.Internal.UV.TCP.Socket

private def after (promise : IO.Promise (Except IO.Error α))
    (next : Except IO.Error α → IO Unit) : IO Unit := do
  let result := promise.result?
  let deliver := fun value => next (value.getD (.error (IO.userError "dropped IO promise")))
  if ← IO.hasFinished result then deliver result.get
  else IO.chainTask result deliver

private def finish (client : Socket) : IO Unit := do
  try after (← client.shutdown) (fun _ => pure ())
  catch _ => pure ()

private inductive Scan where
  | incomplete
  | complete (stop : Nat)
  | invalid

private def scan (bytes : ByteArray) (start scanFrom : Nat) : Scan := Id.run do
  let mut matched : UInt32 := 0
  for i in [scanFrom:bytes.size] do
    if i - start >= 16384 then return .invalid
    let b := bytes[i]!
    matched := if b == 13 then (if matched == 2 then 3 else 1)
      else if b == 10 then (if matched == 1 then 2 else if matched == 3 then 4 else 0)
      else 0
    if matched == 4 then return .complete (i + 1)
  return .incomplete

mutual
  private partial def readNext (client : Socket) (handler : Handler)
      (pending : ByteArray) : IO Unit := do
    try
      after (← client.recv? 8192) fun
        | .ok (some bytes) =>
          process client handler (if pending.isEmpty then bytes else pending ++ bytes)
            0 (pending.size - 3) 0
        | _ => finish client
    catch _ => finish client

  private partial def process (client : Socket) (handler : Handler)
      (bytes : ByteArray) (start scanFrom count : Nat) : IO Unit := do
    if start == bytes.size then
      readNext client handler ByteArray.empty
    else
      match scan bytes start scanFrom with
      | .invalid => finish client
      | .incomplete => readNext client handler (bytes.extract start bytes.size)
      | .complete stop =>
        if count >= 256 then finish client
        else match parse bytes start stop with
        | none => finish client
        | some request =>
          try
            match ← handler request with
            | .ready response => sendNext client handler bytes stop count request.close response
            | .deferred promise =>
              after promise fun
                | .ok response => sendNext client handler bytes stop count request.close response
                | .error _ => finish client
          catch _ => finish client

  private partial def sendNext (client : Socket) (handler : Handler)
      (bytes : ByteArray) (stop count : Nat) (close : Bool) (response : Response) : IO Unit := do
    try
      after (← client.send (if close then response.closing else response.keepAlive)) fun
        | .ok () =>
          if close then finish client
          else process client handler bytes stop stop (count + 1)
        | .error _ => finish client
    catch _ => finish client
end

private partial def acceptNext (server : Socket) (handler : Handler)
    (failed : IO.Promise (Except IO.Error Unit)) : IO Unit := do
  try
    after (← server.accept) fun
      | .error error => failed.resolve (.error error)
      | .ok client => do
        try
          client.noDelay
          readNext client handler ByteArray.empty
        catch _ => finish client
        acceptNext server handler failed
  catch error => failed.resolve (.error error)

/-- Serves until an accept error. Connections share one libuv event loop.
No per-request worker task is created for an immediate handler response. -/
def serve (address : Std.Net.SocketAddress) (handler : Handler) : IO Unit := do
  let server ← Std.Internal.UV.TCP.Socket.new
  server.bind address
  server.listen 1024
  server.noDelay
  let failed ← IO.Promise.new
  acceptNext server handler failed
  match ← IO.wait failed.result? with
  | some result => IO.ofExcept result
  | none => throw (IO.userError "accept loop stopped")

end BaselineHTTP
