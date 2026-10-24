import FastHTTP.Protocol

namespace FastHTTP
namespace Protocol

def wireBody (status : Nat) (isHead : Bool) (body : ByteArray) : ByteArray :=
  if isHead || status == 204 || status == 205 || status == 304 then .empty else body

def responseLength (status : Nat) (body : ByteArray) : Option Nat :=
  if status == 204 then none else some (if status == 205 then 0 else body.size)

end Protocol

/-- Prepared responses, including HEAD variants retaining representation length. -/
structure Response where
  private keepAlive : ByteArray
  private closing : ByteArray
  private legacy : ByteArray
  private payload : ByteArray

def validFieldValue (text : String) : Bool :=
  text.toUTF8.data.all fun b => (b >= 32 && b != 127) || b == 9

def responseFields (headers : Array (String × String)) : Except String String := do
  let mut out := ""
  for (name, value) in headers do
    if name.isEmpty || !name.toUTF8.data.all token || !validFieldValue value then
      throw "invalid response header"
    if ["content-length", "transfer-encoding", "connection", "trailer", "upgrade", "date"].contains name.toLower then
      throw "response framing fields are managed by FastHTTP"
    out := out ++ s!"{name}: {value}\r\n"
  return out

def Response.create (body : ByteArray) (status : Nat := 200) (reason := "OK")
    (contentType := "application/octet-stream")
    (headers : Array (String × String) := #[]) : Except String Response := do
  if status < 200 || status > 599 then throw "expected final HTTP status 200..599"
  if reason.isEmpty || !(reason.toUTF8.data.all fun b => b >= 32 && b < 127) ||
      contentType.isEmpty || !validFieldValue contentType then
    throw "invalid response reason or content type"
  let fields ← responseFields headers
  let length := match Protocol.responseLength status body with
    | none => ""
    | some n => s!"Content-Length: {n}\r\n"
  let headerStart := s!"{status} {reason}\r\n{length}Content-Type: {contentType}\r\n{fields}Connection: "
  let keep := ("HTTP/1.1 " ++ headerStart ++ "keep-alive\r\n").toUTF8
  let close := ("HTTP/1.1 " ++ headerStart ++ "close\r\n").toUTF8
  let legacy := ("HTTP/1.0 " ++ headerStart ++ "close\r\n").toUTF8
  return ⟨keep, close, legacy, Protocol.wireBody status false body⟩

/-- Gather writes share the body and cached Date bytes. No payload copy or header
serialization occurs per request. The server supplies a current Date buffer. -/
def Response.buffers (r : Response) (close isHead : Bool)
    (date : ByteArray := "\r\n".toUTF8) (http10 := false) : Array ByteArray :=
  let header := if http10 then r.legacy else if close then r.closing else r.keepAlive
  if isHead || r.payload.isEmpty then #[header, date] else #[header, date, r.payload]

end FastHTTP
