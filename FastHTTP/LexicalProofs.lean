import FastHTTP.Lexical
import FastHTTP.SyntaxProofs

namespace FastHTTP.Protocol

/-- Every octet in an interval satisfies a separately specified terminal rule. -/
def Octets (bytes : ByteArray) (accept : UInt8 → Prop) (start stop : Nat) : Prop :=
  ∀ i, start ≤ i → i < stop → accept bytes[i]!

def TokenOctet (b : UInt8) : Prop :=
  (65 ≤ b.toNat ∧ b.toNat ≤ 90) ∨ (97 ≤ b.toNat ∧ b.toNat ≤ 122) ∨
  (48 ≤ b.toNat ∧ b.toNat ≤ 57) ∨
  b.toNat ∈ [33,35,36,37,38,39,42,43,45,46,94,95,96,124,126]

def FieldOctet (b : UInt8) : Prop :=
  b.toNat = 9 ∨ b.toNat = 32 ∨ (33 ≤ b.toNat ∧ b.toNat ≤ 126) ∨
    (128 ≤ b.toNat ∧ b.toNat ≤ 255)

theorem token_iff (b : UInt8) : token b = true ↔ TokenOctet b := by
  simp [token, TokenOctet, UInt8.le_iff_toNat_le, UInt8.toNat_ofNat, ← UInt8.toNat_inj] <;> omega

theorem fieldOctet_iff (b : UInt8) : fieldOctet b = true ↔ FieldOctet b := by
  have bound := b.toNat_lt
  simp [fieldOctet, FieldOctet, UInt8.le_iff_toNat_le, UInt8.toNat_ofNat, ← UInt8.toNat_inj] <;> omega

/-- A scan returns the maximal prefix, bounded by stop, including its first
nonmatching octet. This is a statement about every octet, not sampled examples. -/
theorem spanEnd_spec (bytes : ByteArray) (stop : Nat) (accept : UInt8 → Bool) (start : Nat)
    (hs : start ≤ stop) :
    let last := spanEnd bytes stop accept start
    start ≤ last ∧ last ≤ stop ∧ Octets bytes (fun b => accept b = true) start last ∧
      (last = stop ∨ accept bytes[last]! = false) := by
  rw [spanEnd]
  split
  next h =>
    have hi : start < stop ∧ accept bytes[start]! = true := by simpa using h
    have ih := spanEnd_spec bytes stop accept (start + 1) (by omega)
    refine ⟨by omega, ih.2.1, ?_, ih.2.2.2⟩
    intro i hstart hend
    by_cases he : i = start
    · simpa [he] using hi.2
    · exact ih.2.2.1 i (by omega) hend
  next h =>
    refine ⟨by omega, hs, ?_, ?_⟩
    · intro i hstart hend; omega
    · by_cases he : start = stop
      · exact Or.inl he
      · right
        cases ha : accept bytes[start]! <;> simp_all <;> omega
termination_by stop - start

/-- Maximal spans are unique; this is the completeness direction used by the
request-line and field-line parsers. -/
theorem spanEnd_complete (bytes : ByteArray) (stop : Nat) (accept : UInt8 → Bool)
    (start last : Nat) (hs : start ≤ last) (hl : last ≤ stop)
    (ha : Octets bytes (fun b => accept b = true) start last)
    (he : last = stop ∨ accept bytes[last]! = false) :
    spanEnd bytes stop accept start = last := by
  have spec := spanEnd_spec bytes stop accept start (by omega)
  rcases he with he | he
  · subst last
    by_cases hn : spanEnd bytes stop accept start = stop
    · exact hn
    · exfalso
      have valid := ha (spanEnd bytes stop accept start) spec.1 (by omega)
      rcases spec.2.2.2 with h | h <;> simp_all
  · by_cases hn : spanEnd bytes stop accept start = last
    · exact hn
    · exfalso
      by_cases hlt : spanEnd bytes stop accept start < last
      · have valid := ha _ spec.1 hlt
        rcases spec.2.2.2 with h | h <;> simp_all <;> omega
      · have valid := spec.2.2.1 last hs (by omega)
        simp [he] at valid

/-- RFC 9112 field-line envelope, including the CRLF boundary. OWS is included
in the field octet interval and trimmed later when interpreting field values. -/
structure FieldLineGrammar (bytes : ByteArray) (stop : Nat) (field : FieldLine) : Prop where
  bounds : field.start < field.colon ∧ field.next ≤ stop ∧ stop ≤ bytes.size
  valueStart : field.valueStart = field.colon + 1
  next : field.next = field.valueEnd + 2
  valueBounds : field.valueStart ≤ field.valueEnd
  name : Octets bytes TokenOctet field.start field.colon
  colon : bytes[field.colon]! = 58
  value : Octets bytes FieldOctet field.valueStart field.valueEnd
  cr : bytes[field.valueEnd]! = 13
  lf : bytes[field.valueEnd + 1]! = 10

/-- Every successful production field scan satisfies the independent envelope. -/
theorem parseFieldLine_sound (bytes : ByteArray) (start stop : Nat) (field : FieldLine)
    (h : parseFieldLine bytes start stop = some field) :
    field.start = start ∧ FieldLineGrammar bytes stop field := by
  unfold parseFieldLine at h
  split at h
  · contradiction
  · rename_i hb
    have hbounds : start < stop ∧ stop ≤ bytes.size := by simpa using hb
    have name := spanEnd_spec bytes stop token start (by omega)
    dsimp only at h
    split at h
    · contradiction
    · rename_i hc
      have hcolon : spanEnd bytes stop token start ≠ start ∧
          spanEnd bytes stop token start < stop ∧ bytes[spanEnd bytes stop token start]! = 58 := by
        simpa [Bool.or_eq_true, beq_iff_eq, and_assoc] using hc
      have value := spanEnd_spec bytes stop fieldOctet (spanEnd bytes stop token start + 1) (by omega)
      try dsimp only at h
      split at h
      · contradiction
      · rename_i he
        have hend : spanEnd bytes stop fieldOctet (spanEnd bytes stop token start + 1) + 2 ≤ stop ∧
            bytes[spanEnd bytes stop fieldOctet (spanEnd bytes stop token start + 1)]! = 13 ∧
            bytes[spanEnd bytes stop fieldOctet (spanEnd bytes stop token start + 1) + 1]! = 10 := by
          simpa [Bool.or_eq_true, beq_iff_eq, and_assoc] using he
        cases h
        refine ⟨rfl, ⟨?_, rfl, rfl, value.1, ?_, hcolon.2.2, ?_, hend.2.1, hend.2.2⟩⟩
        · exact ⟨by dsimp only; omega, hend.1, hbounds.2⟩
        · intro i hi hj; exact (token_iff _).mp (name.2.2.1 i hi hj)
        · intro i hi hj; exact (fieldOctet_iff _).mp (value.2.2.1 i hi hj)

/-- Every well-formed field envelope is accepted with its exact boundaries. -/
theorem parseFieldLine_complete (bytes : ByteArray) (stop : Nat) (field : FieldLine)
    (hg : FieldLineGrammar bytes stop field) :
    parseFieldLine bytes field.start stop = some field := by
  rcases field with ⟨start, colon, valueStart, valueEnd, next⟩
  rcases hg with ⟨bounds, hs, hnxt, vb, name, hc, value, cr, lf⟩
  simp only at bounds hs hnxt vb name hc value cr lf ⊢
  subst valueStart next
  have hn := spanEnd_complete bytes stop token start colon (by omega) (by omega)
    (fun i hi hj => (token_iff _).mpr (name i hi hj)) (Or.inr (by simp [hc, token]))
  have hv := spanEnd_complete bytes stop fieldOctet (colon + 1) valueEnd vb (by omega)
    (fun i hi hj => (fieldOctet_iff _).mpr (value i hi hj)) (Or.inr (by simp [cr, fieldOctet]))
  have hstart : ¬start ≥ stop := by omega
  have hsize : ¬stop > bytes.size := by omega
  have hcolon : ¬colon ≥ stop := by omega
  have hne : colon ≠ start := by omega
  have hend : ¬valueEnd + 2 > stop := by omega
  simp [parseFieldLine, hstart, hsize, hn, hv, hcolon, hne, hend, hc, cr, lf]

/-- Exact soundness/completeness, including the starting cursor. -/
theorem parseFieldLine_iff (bytes : ByteArray) (start stop : Nat) (field : FieldLine) :
    parseFieldLine bytes start stop = some field ↔
      field.start = start ∧ FieldLineGrammar bytes stop field := by
  constructor
  · exact parseFieldLine_sound bytes start stop field
  · rintro ⟨rfl, hg⟩; exact parseFieldLine_complete bytes stop field hg

def TargetOctet (b : UInt8) : Prop := 33 ≤ b.toNat ∧ b.toNat ≤ 126 ∧ b.toNat ≠ 35

theorem targetOctet_iff (b : UInt8) : targetOctet b = true ↔ TargetOctet b := by
  simp [targetOctet, TargetOctet, UInt8.le_iff_toNat_le, UInt8.toNat_ofNat, ← UInt8.toNat_inj, and_assoc]

/-- RFC 9112 request-line envelope. URI productions and method semantics are
separate from this mandatory token / SP / target / SP / HTTP-version CRLF rule. -/
structure RequestLineGrammar (bytes : ByteArray) (stop : Nat) (line : RequestLine) : Prop where
  bounds : line.methodStart < line.methodEnd ∧ line.targetStart < line.targetEnd ∧
    line.headersStart ≤ stop ∧ stop ≤ bytes.size
  targetStart : line.targetStart = line.methodEnd + 1
  headersStart : line.headersStart = line.targetEnd + 11
  method : Octets bytes TokenOctet line.methodStart line.methodEnd
  target : Octets bytes TargetOctet line.targetStart line.targetEnd
  methodSpace : bytes[line.methodEnd]! = 32
  targetSpace : bytes[line.targetEnd]! = 32
  version : bytes[line.targetEnd + 1]! = 72 ∧ bytes[line.targetEnd + 2]! = 84 ∧
    bytes[line.targetEnd + 3]! = 84 ∧ bytes[line.targetEnd + 4]! = 80 ∧
    bytes[line.targetEnd + 5]! = 47 ∧ bytes[line.targetEnd + 6]! = 49 ∧
    bytes[line.targetEnd + 7]! = 46
  minor : bytes[line.targetEnd + 8]!.toNat = 48 + line.minor ∧ line.minor ≤ 9
  crlf : bytes[line.targetEnd + 9]! = 13 ∧ bytes[line.targetEnd + 10]! = 10

/-- Accepted request-line metadata exactly describes the wire envelope. -/
theorem parseRequestLine_sound (bytes : ByteArray) (start stop maxTarget : Nat) (line : RequestLine)
    (h : parseRequestLine bytes start stop maxTarget = .ok line) :
    line.methodStart = start ∧ RequestLineGrammar bytes stop line ∧
      line.targetEnd - line.targetStart ≤ maxTarget := by
  unfold parseRequestLine at h
  split at h
  · contradiction
  · rename_i hb
    have hbounds : start < stop ∧ stop ≤ bytes.size := by simpa using hb
    have name := spanEnd_spec bytes stop token start (by omega)
    dsimp only at h
    split at h
    · contradiction
    · rename_i hm
      have hmethod : spanEnd bytes stop token start ≠ start ∧
          spanEnd bytes stop token start < stop ∧ bytes[spanEnd bytes stop token start]! = 32 := by
        simpa [Bool.or_eq_true, beq_iff_eq, and_assoc] using hm
      have target := spanEnd_spec bytes stop targetOctet (spanEnd bytes stop token start + 1) (by omega)
      try dsimp only at h
      split at h
      · contradiction
      · rename_i ht
        have htarget : spanEnd bytes stop targetOctet (spanEnd bytes stop token start + 1) ≠
            spanEnd bytes stop token start + 1 ∧
            spanEnd bytes stop targetOctet (spanEnd bytes stop token start + 1) < stop ∧
            bytes[spanEnd bytes stop targetOctet (spanEnd bytes stop token start + 1)]! = 32 := by
          simpa [Bool.or_eq_true, beq_iff_eq, and_assoc] using ht
        split at h
        · contradiction
        · rename_i hlength
          split at h
          · contradiction
          · rename_i hv
            have version := hv
            simp [and_assoc] at version
            try dsimp only at h
            split at h
            · contradiction
            · rename_i hd
              have digits := hd
              simp [UInt8.lt_iff_toNat_lt, UInt8.toNat_ofNat, and_assoc] at digits
              split at h
              · contradiction
              · rename_i hmajor
                have major : bytes[spanEnd bytes stop targetOctet (spanEnd bytes stop token start + 1) + 6]! = 49 := by
                  simpa using hmajor
                cases h
                refine ⟨rfl, ?_, by dsimp only; omega⟩
                refine ⟨?_, rfl, rfl, ?_, ?_, hmethod.2.2, htarget.2.2, ?_, ?_, ?_⟩
                · dsimp only; omega
                · intro i hi hj; exact (token_iff _).mp (name.2.2.1 i hi hj)
                · intro i hi hj; exact (targetOctet_iff _).mp (target.2.2.1 i hi hj)
                · simp_all
                · dsimp only; omega
                · simp_all

/-- Completeness for every supported HTTP/1.x envelope within the target limit. -/
theorem parseRequestLine_complete (bytes : ByteArray) (stop maxTarget : Nat) (line : RequestLine)
    (hg : RequestLineGrammar bytes stop line)
    (hl : line.targetEnd - line.targetStart ≤ maxTarget) :
    parseRequestLine bytes line.methodStart stop maxTarget = .ok line := by
  rcases line with ⟨start, methodEnd, targetStart, targetEnd, headersStart, minor⟩
  rcases hg with ⟨bounds, hts, hhs, name, target, ms, ts, version, hminor, crlf⟩
  simp only at bounds hts hhs name target ms ts version hminor crlf hl ⊢
  subst targetStart headersStart
  have hn := spanEnd_complete bytes stop token start methodEnd (by omega) (by omega)
    (fun i hi hj => (token_iff _).mpr (name i hi hj)) (Or.inr (by simp [ms, token]))
  have ht := spanEnd_complete bytes stop targetOctet (methodEnd + 1) targetEnd (by omega) (by omega)
    (fun i hi hj => (targetOctet_iff _).mpr (target i hi hj)) (Or.inr (by simp [ts, targetOctet]))
  have hstart : ¬start ≥ stop := by omega
  have hsize : ¬stop > bytes.size := by omega
  have hmethod : methodEnd ≠ start := by omega
  have hmethodStop : ¬methodEnd ≥ stop := by omega
  have htarget : targetEnd ≠ methodEnd + 1 := by omega
  have htargetStop : ¬targetEnd ≥ stop := by omega
  have hlength : ¬targetEnd - (methodEnd + 1) > maxTarget := by omega
  have hend : ¬targetEnd + 11 > stop := by omega
  have hmin : ¬bytes[targetEnd + 8]! < 48 := by
    simp only [UInt8.lt_iff_toNat_lt, UInt8.toNat_ofNat]; omega
  have hmax : ¬bytes[targetEnd + 8]! > 57 := by
    simp only [UInt8.lt_iff_toNat_lt, UInt8.toNat_ofNat]; omega
  have hm : bytes[targetEnd + 8]!.toNat - 48 = minor := by omega
  simp [parseRequestLine, hstart, hsize, hn, ht, hmethod, hmethodStop, htarget, htargetStop,
    hlength, hend, ms, ts, version.1, version.2.1, version.2.2.1, version.2.2.2.1,
    version.2.2.2.2.1, version.2.2.2.2.2.1, version.2.2.2.2.2.2, crlf.1, crlf.2, hmin, hmax, hm]

theorem parseRequestLine_iff (bytes : ByteArray) (start stop maxTarget : Nat) (line : RequestLine) :
    parseRequestLine bytes start stop maxTarget = .ok line ↔
      line.methodStart = start ∧ RequestLineGrammar bytes stop line ∧
        line.targetEnd - line.targetStart ≤ maxTarget := by
  constructor
  · exact parseRequestLine_sound bytes start stop maxTarget line
  · rintro ⟨rfl, hg, hl⟩; exact parseRequestLine_complete bytes stop maxTarget line hg hl

end FastHTTP.Protocol
