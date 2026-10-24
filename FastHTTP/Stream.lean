import FastHTTP.Response

namespace FastHTTP

/-- A per-request pull producer. Resolve `none` at EOF; each `some` must be nonempty.
The server asks for another chunk only after the previous write completes.
`release` runs once on completion, producer/write error, or HEAD suppression;
it must return promptly. Pending producer cancellation is not implemented. -/
structure StreamResponse where
  private keepAlive : ByteArray
  private closing : ByteArray
  private legacy : ByteArray
  next : IO (IO.Promise (Except IO.Error (Option ByteArray)))
  release : IO Unit

def StreamResponse.create (next : IO (IO.Promise (Except IO.Error (Option ByteArray))))
    (release : IO Unit := pure ()) (status : Nat := 200) (reason := "OK")
    (headers : Array (String × String) := #[]) : Except String StreamResponse := do
  if status < 200 || status > 599 || status == 204 || status == 205 || status == 304 then
    throw "streaming response requires a status allowing a body"
  if reason.isEmpty || !(reason.toUTF8.data.all fun b => b >= 32 && b < 127) then
    throw "invalid response reason"
  let fields ← responseFields headers
  let start := s!"HTTP/1.1 {status} {reason}\r\nTransfer-Encoding: chunked\r\n{fields}Connection: "
  return ⟨(start ++ "keep-alive\r\n").toUTF8,
    (start ++ "close\r\n").toUTF8,
    s!"HTTP/1.0 {status} {reason}\r\n{fields}Connection: close\r\n".toUTF8, next, release⟩

def StreamResponse.head (r : StreamResponse) (close : Bool) : ByteArray :=
  (if close then r.closing else r.keepAlive) ++ "\r\n".toUTF8

def StreamResponse.buffers (r : StreamResponse) (close http10 : Bool) (date : ByteArray) : Array ByteArray :=
  #[if http10 then r.legacy else if close then r.closing else r.keepAlive, date]

/-- ByteArray.size, not String.length, determines the chunk's declared byte count. -/
def encodeChunk (bytes : ByteArray) : Array ByteArray :=
  #[(String.ofList (Nat.toDigits 16 bytes.size) ++ "\r\n").toUTF8, bytes, "\r\n".toUTF8]

end FastHTTP
