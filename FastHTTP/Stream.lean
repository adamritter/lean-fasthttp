import FastHTTP.Response

namespace FastHTTP

/-- A per-request pull producer. Resolve `none` at EOF; each `some` must be nonempty.
The server asks for another chunk only after the previous write completes.
`release` runs once on completion, producer/write error, or HEAD suppression;
it must return promptly. Pending producer cancellation is not implemented. -/
structure StreamResponse where
  keepAlive : ByteArray
  closing : ByteArray
  legacy : ByteArray
  next : IO (IO.Promise (Except IO.Error (Option ByteArray)))
  release : IO Unit
  grammar : Protocol.StreamingGrammar keepAlive closing legacy

def StreamResponse.create (next : IO (IO.Promise (Except IO.Error (Option ByteArray))))
    (release : IO Unit := pure ()) (status : Nat := 200) (reason := "OK")
    (headers : Array (String × String) := #[]) : Except String StreamResponse := do
  if hs : 200 ≤ status ∧ status ≤ 599 ∧ status ≠ 204 ∧ status ≠ 205 ∧ status ≠ 304 then
    if hr : Protocol.validOutputReason reason then
      let fields ← checkedResponseFields Protocol.managedResponseFields [] headers.toList
      let start := s!"HTTP/1.1 {status} {reason}\r\nTransfer-Encoding: chunked\r\n{fields.val}Connection: "
      return ⟨(start ++ "keep-alive\r\n").toUTF8,
        (start ++ "close\r\n").toUTF8,
        s!"HTTP/1.0 {status} {reason}\r\n{fields.val}Connection: close\r\n".toUTF8, next, release, by
          refine ⟨status, reason, fields.val, headers.toList, hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1,
            hs.2.2.2.2, (Protocol.validOutputReason_iff reason).mp hr, fields.property, ?_, ?_, ?_⟩
          all_goals simp [start, Protocol.StreamingHeadWire, toString, String.append_assoc]⟩
    else throw "invalid response reason"
  else throw "streaming response requires a status allowing a body"

def StreamResponse.head (r : StreamResponse) (close : Bool) : ByteArray :=
  (if close then r.closing else r.keepAlive) ++ "\r\n".toUTF8

def StreamResponse.buffers (r : StreamResponse) (close http10 : Bool) (date : ByteArray) : Array ByteArray :=
  #[if http10 then r.legacy else if close then r.closing else r.keepAlive, date]

/-- ByteArray.size, not String.length, determines the chunk's declared byte count. -/
def encodeChunk (bytes : ByteArray) : Array ByteArray :=
  #[(String.ofList (Nat.toDigits 16 bytes.size) ++ "\r\n").toUTF8, bytes, "\r\n".toUTF8]

end FastHTTP
