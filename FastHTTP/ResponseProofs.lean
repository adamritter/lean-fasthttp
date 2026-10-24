import FastHTTP.Driver
import FastHTTP.WireProofs
import LeanUV.AdapterContract

namespace FastHTTP.Protocol

/-- RFC status-code is exactly three ASCII decimal octets. -/
theorem status_wire_encoding (status : Nat) (low : 200 ≤ status) (high : status ≤ 599) :
    (toString status).toUTF8.size = 3 ∧ DecimalEncoding (toString status).toUTF8.data.toList status := by
  refine ⟨?_, decimal_wire_encoding status⟩
  have upper : (Nat.toDigits 10 status).length ≤ 3 :=
    (Nat.length_toDigits_le_iff (by decide) (by decide)).mpr (by omega)
  have lower : ¬(Nat.toDigits 10 status).length ≤ 2 := by
    rw [Nat.length_toDigits_le_iff (by decide) (by decide)]
    omega
  have count : (Nat.toDigits 10 status).length = 3 := by omega
  have bytes := numeral_single_byte (Nat.toDigits 10 status)
    (fun c hc => (numeral_alphabet 10 status (by decide) (by decide) c hc).1)
  rw [Nat.toString_eq_ofList_toDigits]
  have lengths := congrArg List.length bytes
  simpa [count] using lengths

abbrev wireBytes (buffers : Array ByteArray) : List UInt8 := LeanUV.TCP.Contract.flatten buffers.toList

/-- Complete finite response production. The application representation is an
arbitrary binary body; its exact declared length and suppression rules are part
of this grammar, not external assumptions. Date includes the final empty line. -/
def PreparedOutputGrammar (close isHead http10 : Bool) (wire : List UInt8) : Prop :=
  ∃ status reason contentType fields headers body date,
    200 ≤ status ∧ status ≤ 599 ∧
    (toString status).toUTF8.size = 3 ∧ DecimalEncoding (toString status).toUTF8.data.toList status ∧
    OutputReasonGrammar reason ∧ 0 < contentType.utf8ByteSize ∧ OutputValueGrammar contentType ∧
    OutputFields ("content-type" :: managedResponseFields) [] headers fields ∧ DateHeaderGrammar date ∧
    (∀ n, responseLength status body = some n → DecimalEncoding (toString n).toUTF8.data.toList n) ∧
    wire = (PreparedHeadWire status reason contentType fields body http10 (http10 || close)).data.toList ++
      date.data.toList ++ (wireBody status isHead body).data.toList

/-- Complete streaming head production. HTTP/1.1 has one chunked coding and no
Content-Length; HTTP/1.0 has neither and must close. Managed fields cannot be
introduced by application headers. -/
def StreamingOutputGrammar (close http10 : Bool) (wire : List UInt8) : Prop :=
  ∃ status reason fields headers date,
    200 ≤ status ∧ status ≤ 599 ∧ status ≠ 204 ∧ status ≠ 205 ∧ status ≠ 304 ∧
    (toString status).toUTF8.size = 3 ∧ DecimalEncoding (toString status).toUTF8.data.toList status ∧
    OutputReasonGrammar reason ∧ OutputFields managedResponseFields [] headers fields ∧ DateHeaderGrammar date ∧
    wire = (StreamingHeadWire status reason fields http10 (http10 || close)).data.toList ++ date.data.toList

theorem prepared_buffers_grammar (response : Response) (date : DateHeader) (close isHead http10 : Bool) :
    PreparedOutputGrammar close isHead http10 (wireBytes (response.buffers close isHead date.bytes http10)) := by
  obtain ⟨status, reason, contentType, fields, body, headers, low, high, reasonOK, contentNonempty,
    contentOK, fieldsOK, keep, closing, legacy, payload⟩ := response.grammar
  refine ⟨status, reason, contentType, fields, headers, body, date.bytes, low, high,
    (status_wire_encoding status low high).1, (status_wire_encoding status low high).2,
    reasonOK, contentNonempty, contentOK, fieldsOK, date.grammar,
    fun n _ => decimal_wire_encoding n, ?_⟩
  have bodyRule : response.payload = wireBody status false body := by
    rcases payload with ⟨bodyless, empty⟩ | ⟨ordinary, full⟩
    · rcases bodyless with h | h | h <;> simp [wireBody, h, empty]
    · simp [wireBody, ordinary.1, ordinary.2.1, ordinary.2.2, full]
  have emptyPayload : response.payload.isEmpty = true → response.payload.data.toList = [] := by
    intro empty
    have h : response.payload = .empty := by simpa [ByteArray.isEmpty] using empty
    rw [h]
    rfl
  cases http10 <;> cases close <;> cases isHead <;>
    simp only [Response.buffers, Bool.false_or, Bool.true_or, Bool.or_false, Bool.or_true,
      Bool.false_eq_true, ↓reduceIte]
  all_goals try split
  all_goals simp_all [wireBytes, LeanUV.TCP.Contract.flatten, wireBody, List.append_assoc]

theorem streaming_buffers_grammar (response : StreamResponse) (date : DateHeader) (close http10 : Bool) :
    StreamingOutputGrammar close http10 (wireBytes (response.buffers close http10 date.bytes)) := by
  obtain ⟨status, reason, fields, headers, low, high, h204, h205, h304, reasonOK,
    fieldsOK, keep, closing, legacy⟩ := response.grammar
  refine ⟨status, reason, fields, headers, date.bytes, low, high, h204, h205, h304,
    (status_wire_encoding status low high).1, (status_wire_encoding status low high).2,
    reasonOK, fieldsOK, date.grammar, ?_⟩
  cases http10 <;> cases close <;>
    simp [StreamResponse.buffers, keep, closing, legacy, wireBytes, LeanUV.TCP.Contract.flatten]

/-- A nonterminal chunk has a nonempty payload and a nonempty ASCII hexadecimal
length with exactly its byte count. A terminal chunk is a separate production. -/
def ChunkOutputGrammar (payload : ByteArray) (wire : List UInt8) : Prop :=
  payload.size > 0 ∧ ∃ digits : ByteArray,
    digits.size > 0 ∧ (∀ b ∈ digits.data.toList, HexOctet b) ∧ numeralValue 16 digits = payload.size ∧
    wire = digits.data.toList ++ "\r\n".toUTF8.data.toList ++ payload.data.toList ++ "\r\n".toUTF8.data.toList

theorem encoded_chunk_grammar (payload : ByteArray) (nonempty : payload.isEmpty = false) :
    ChunkOutputGrammar payload (wireBytes (encodeChunk payload)) := by
  have positive : payload.size > 0 := by
    have h : payload ≠ .empty := by simpa [ByteArray.isEmpty] using nonempty
    apply Nat.pos_of_ne_zero
    intro zero
    exact h (ByteArray.size_eq_zero_iff.mp zero)
  refine ⟨positive, numeralBytes 16 payload.size, ?_, ?_, (encodeChunk_wire payload).2, ?_⟩
  · have bytes := numeral_single_byte (Nat.toDigits 16 payload.size)
      (fun c hc => (numeral_alphabet 16 payload.size (by decide) (by decide) c hc).1)
    have lengths := congrArg List.length bytes
    have count : 0 < (Nat.toDigits 16 payload.size).length := Nat.length_toDigits_pos
    simp only [List.length_map, Array.length_toList] at lengths
    change 0 < (String.ofList (Nat.toDigits 16 payload.size)).toUTF8.data.size
    omega
  · intro b member
    have bytes := numeral_single_byte (Nat.toDigits 16 payload.size)
      (fun c hc => (numeral_alphabet 16 payload.size (by decide) (by decide) c hc).1)
    change b ∈ (String.ofList (Nat.toDigits 16 payload.size)).toUTF8.data.toList at member
    rw [bytes] at member
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp member
    exact (hexValue_iff _).mp (numeral_alphabet 16 payload.size (by decide) (by decide) c hc).2
  · rw [(encodeChunk_wire payload).1]
    simp [wireBytes, LeanUV.TCP.Contract.flatten, List.append_assoc]

/-- These productions cover every response header selected by the real driver,
including close-on-error responses and HEAD/legacy specialization. -/
theorem driver_prepared_buffers_grammar (purpose : Driver.Purpose) (response : Response) (date : DateHeader) :
    match purpose with
    | .rejection => PreparedOutputGrammar true false false (wireBytes (Driver.preparedBuffers purpose response date))
    | .response request _ => PreparedOutputGrammar request.close request.isHead (request.versionMinor == 0)
        (wireBytes (Driver.preparedBuffers purpose response date)) := by
  cases purpose <;> exact prepared_buffers_grammar response date _ _ _

end FastHTTP.Protocol
