import FastHTTP.Protocol
import FastHTTP.ResponseChecked

namespace FastHTTP.Protocol

def wireBody (status : Nat) (isHead : Bool) (body : ByteArray) : ByteArray :=
  if isHead || status == 204 || status == 205 || status == 304 then .empty else body

def responseLength (status : Nat) (body : ByteArray) : Option Nat :=
  if status == 204 then none else some (if status == 205 then 0 else body.size)

/-- Grammar production for a prepared response head, before its Date field and
empty line. Status and decimal numeral semantics are proved in ResponseProofs.
User fields occur only in the independently validated OutputFields production. -/
def PreparedHeadWire (status : Nat) (reason contentType fields : String) (body : ByteArray)
    (http10 close : Bool) : ByteArray :=
  ((if http10 then "HTTP/1.0 " else "HTTP/1.1 ") ++ toString status ++ " " ++ reason ++ "\r\n" ++
    (if status = 204 then "" else "Content-Length: " ++ toString (if status = 205 then 0 else body.size) ++ "\r\n") ++
    "Content-Type: " ++ contentType ++ "\r\n" ++ fields ++ "Connection: " ++
    (if close then "close" else "keep-alive") ++ "\r\n").toUTF8

def PreparedGrammar (keepAlive closing legacy payload : ByteArray) : Prop :=
  ∃ status reason contentType fields body headers,
    200 ≤ status ∧ status ≤ 599 ∧ OutputReasonGrammar reason ∧
    0 < contentType.utf8ByteSize ∧ OutputValueGrammar contentType ∧
    OutputFields ("content-type" :: managedResponseFields) [] headers fields ∧
    keepAlive = PreparedHeadWire status reason contentType fields body false false ∧
    closing = PreparedHeadWire status reason contentType fields body false true ∧
    legacy = PreparedHeadWire status reason contentType fields body true true ∧
    ((status = 204 ∨ status = 205 ∨ status = 304) ∧ payload = .empty ∨
      (status ≠ 204 ∧ status ≠ 205 ∧ status ≠ 304) ∧ payload = body)

/-- Streaming uses chunked framing only for HTTP/1.1; the HTTP/1.0 production is
close-delimited. Bodyless statuses are excluded before a producer is acquired. -/
def StreamingHeadWire (status : Nat) (reason fields : String) (http10 close : Bool) : ByteArray :=
  ((if http10 then "HTTP/1.0 " else "HTTP/1.1 ") ++ toString status ++ " " ++ reason ++ "\r\n" ++
    (if http10 then "" else "Transfer-Encoding: chunked\r\n") ++ fields ++ "Connection: " ++
    (if close then "close" else "keep-alive") ++ "\r\n").toUTF8

def StreamingGrammar (keepAlive closing legacy : ByteArray) : Prop :=
  ∃ status reason fields headers,
    200 ≤ status ∧ status ≤ 599 ∧ status ≠ 204 ∧ status ≠ 205 ∧ status ≠ 304 ∧
    OutputReasonGrammar reason ∧ OutputFields managedResponseFields [] headers fields ∧
    keepAlive = StreamingHeadWire status reason fields false false ∧
    closing = StreamingHeadWire status reason fields false true ∧
    legacy = StreamingHeadWire status reason fields true true

end FastHTTP.Protocol
