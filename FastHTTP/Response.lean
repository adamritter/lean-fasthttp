import FastHTTP.ResponseModel

namespace FastHTTP

/-- Prepared responses carry an erased grammar certificate. Even constructing or
updating the record directly requires proving its wire fields and framing valid. -/
structure Response where
  keepAlive : ByteArray
  closing : ByteArray
  legacy : ByteArray
  payload : ByteArray
  grammar : Protocol.PreparedGrammar keepAlive closing legacy payload

def Response.create (body : ByteArray) (status : Nat := 200) (reason := "OK")
    (contentType := "application/octet-stream")
    (headers : Array (String × String) := #[]) : Except String Response := do
  if hs : 200 ≤ status ∧ status ≤ 599 then
    if hr : Protocol.validOutputReason reason then
      if hc : 0 < contentType.utf8ByteSize ∧ validFieldValue contentType = true then
        let fields ← checkedResponseFields ("content-type" :: Protocol.managedResponseFields) [] headers.toList
        let length := match Protocol.responseLength status body with
          | none => ""
          | some n => s!"Content-Length: {n}\r\n"
        let headerStart := s!"{status} {reason}\r\n{length}Content-Type: {contentType}\r\n{fields.val}Connection: "
        let keep := ("HTTP/1.1 " ++ headerStart ++ "keep-alive\r\n").toUTF8
        let close := ("HTTP/1.1 " ++ headerStart ++ "close\r\n").toUTF8
        let legacy := ("HTTP/1.0 " ++ headerStart ++ "close\r\n").toUTF8
        return ⟨keep, close, legacy, Protocol.wireBody status false body, by
          refine ⟨status, reason, contentType, fields.val, body, headers.toList, hs.1, hs.2,
            (Protocol.validOutputReason_iff reason).mp hr, hc.1,
            (Protocol.validFieldValue_iff contentType).mp hc.2, fields.property, ?_, ?_, ?_, ?_⟩
          · by_cases emptyLength : status = 204 <;>
              simp [keep, headerStart, length, Protocol.responseLength, Protocol.PreparedHeadWire, emptyLength, toString, String.append_assoc]
          · by_cases emptyLength : status = 204 <;>
              simp [close, headerStart, length, Protocol.responseLength, Protocol.PreparedHeadWire, emptyLength, toString, String.append_assoc]
          · by_cases emptyLength : status = 204 <;>
              simp [legacy, headerStart, length, Protocol.responseLength, Protocol.PreparedHeadWire, emptyLength, toString, String.append_assoc]
          · by_cases h204 : status = 204 <;> by_cases h205 : status = 205 <;> by_cases h304 : status = 304 <;>
              simp [Protocol.wireBody, h204, h205, h304]⟩
      else throw "invalid response content type"
    else throw "invalid response reason"
  else throw "expected final HTTP status 200..599"

/-- Gather writes share the body and cached Date bytes. No payload copy or header
serialization occurs per request. The server supplies a current Date buffer. -/
def Response.buffers (r : Response) (close isHead : Bool)
    (date : ByteArray := "\r\n".toUTF8) (http10 := false) : Array ByteArray :=
  let header := if http10 then r.legacy else if close then r.closing else r.keepAlive
  if isHead || r.payload.isEmpty then #[header, date] else #[header, date, r.payload]

end FastHTTP
