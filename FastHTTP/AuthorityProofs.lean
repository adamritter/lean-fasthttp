import FastHTTP.Authority
import FastHTTP.IPv6Proofs
import FastHTTP.LexicalProofs

namespace FastHTTP.Protocol

/-- RFC 3986 reg-name literal alphabet. Percent-escapes have their own production. -/
def RegNameOctet (b : UInt8) : Prop :=
  (65 ≤ b.toNat ∧ b.toNat ≤ 90) ∨ (97 ≤ b.toNat ∧ b.toNat ≤ 122) ∨
  (48 ≤ b.toNat ∧ b.toNat ≤ 57) ∨
  b.toNat ∈ [45,46,95,126,33,36,38,39,40,41,42,43,44,59,61]

def FutureOctet (b : UInt8) : Prop := RegNameOctet b ∨ b.toNat = 58

theorem regNameOctet_iff (b : UInt8) :
    (unreserved b || subDelimiter b) = true ↔ RegNameOctet b := by
  simp [unreserved, subDelimiter, RegNameOctet, UInt8.le_iff_toNat_le, ← UInt8.toNat_inj] <;> omega

theorem futureOctet_iff (b : UInt8) : futureOctet b = true ↔ FutureOctet b := by
  unfold futureOctet
  rw [Bool.or_eq_true, regNameOctet_iff]
  simp [FutureOctet, ← UInt8.toNat_inj]

theorem decimalOctet_iff (b : UInt8) : decimalOctet b = true ↔ DecimalOctet b := by
  simp [decimalOctet, DecimalOctet, UInt8.le_iff_toNat_le]

theorem spanEnd_eq_stop_iff (bytes : ByteArray) (start stop : Nat) (p : UInt8 → Bool)
    (hs : start ≤ stop) :
    spanEnd bytes stop p start = stop ↔ Octets bytes (fun b => p b = true) start stop := by
  constructor
  · intro h
    have spec := spanEnd_spec bytes stop p start hs
    simpa [h] using spec.2.2.1
  · intro h
    exact spanEnd_complete bytes stop p start stop hs (by omega) h (Or.inl rfl)

/-- Independent IPvFuture production: (v / V) 1*HEXDIG '.' 1*(unreserved / sub-delims / ':'). -/
def IPvFutureGrammar (bytes : ByteArray) (start stop : Nat) : Prop :=
  stop ≤ bytes.size ∧ (bytes[start]! = 118 ∨ bytes[start]! = 86) ∧
  ∃ dot, start + 1 < dot ∧ dot + 1 < stop ∧ bytes[dot]! = 46 ∧
    Octets bytes HexOctet (start + 1) dot ∧ Octets bytes FutureOctet (dot + 1) stop

theorem validIPvFuture_iff (bytes : ByteArray) (start stop : Nat) :
    validIPvFuture bytes start stop = true ↔ IPvFutureGrammar bytes start stop := by
  constructor
  · intro h
    unfold validIPvFuture at h
    split at h
    · rename_i hb
      have hb' : start < stop ∧ stop ≤ bytes.size ∧ (bytes[start]! = 118 ∨ bytes[start]! = 86) := by
        simpa [and_assoc] using hb
      have hs := spanEnd_spec bytes stop hexDigit (start + 1) (by omega)
      have hh : start + 1 < spanEnd bytes stop hexDigit (start + 1) ∧
          spanEnd bytes stop hexDigit (start + 1) < stop ∧
          bytes[spanEnd bytes stop hexDigit (start + 1)]! = 46 ∧
          spanEnd bytes stop hexDigit (start + 1) + 1 < stop ∧
          spanEnd bytes stop futureOctet (spanEnd bytes stop hexDigit (start + 1) + 1) = stop := by
        simpa [and_assoc] using h
      refine ⟨hb'.2.1, hb'.2.2, _, hh.1, hh.2.2.2.1, hh.2.2.1,
        (fun i hi hj => (hexDigit_iff _).mp (hs.2.2.1 i hi hj)), ?_⟩
      have run := (spanEnd_eq_stop_iff bytes _ stop futureOctet (by omega)).mp hh.2.2.2.2
      exact fun i hi hj => (futureOctet_iff _).mp (run i hi hj)
    · contradiction
  · rintro ⟨hb, hv, dot, hd, he, hdot, hx, ht⟩
    have scan := spanEnd_complete bytes stop hexDigit (start + 1) dot (by omega) (by omega)
      (fun i hi hj => (hexDigit_iff _).mpr (hx i hi hj))
      (Or.inr (by simp [hdot, hexDigit, lower]))
    have tail := (spanEnd_eq_stop_iff bytes (dot + 1) stop futureOctet (by omega)).mpr
      (fun i hi hj => (futureOctet_iff _).mpr (ht i hi hj))
    simp [validIPvFuture, show start < stop by omega, hb, hv, scan, hd, he, hdot, tail,
      show dot < stop by omega, -getElem!_pos]

/-- The bracket interior is a nonempty IPv6 or IPvFuture address. The explicit
closing-bracket exclusion is the literal lexical boundary of both productions. -/
def IPLiteralGrammar (bytes : ByteArray) (start stop : Nat) : Prop :=
  start < stop ∧ stop ≤ bytes.size ∧ Octets bytes (fun b => b ≠ 93) start stop ∧
    ((∃ text, String.fromUTF8? (bytes.extract start stop) = some text ∧ IPv6Grammar text) ∨
      IPvFutureGrammar bytes start stop)

theorem validIPLiteral_iff (bytes : ByteArray) (start stop : Nat) :
    validIPLiteral bytes start stop = true ↔ IPLiteralGrammar bytes start stop := by
  by_cases hs : start < stop
  · simp only [validIPLiteral, IPLiteralGrammar, Bool.and_eq_true, Bool.or_eq_true,
      decide_eq_true_eq, beq_iff_eq, hs, true_and, spanEnd_eq_stop_iff bytes start stop _ (by omega),
      utf8IPv6_iff, validIPvFuture_iff, bne_iff_ne, and_assoc]
  · simp [validIPLiteral, IPLiteralGrammar, hs]

/-- A port suffix is absent or ':' followed by decimal digits. For CONNECT the
suffix and at least one digit are mandatory. No machine integer limit is imposed. -/
def PortGrammar (bytes : ByteArray) (start stop : Nat) (required : Bool) : Prop :=
  (start = stop ∧ required = false) ∨
    (start < stop ∧ bytes[start]! = 58 ∧ (required = false ∨ start + 1 < stop) ∧
      Octets bytes DecimalOctet (start + 1) stop)

theorem validPort_iff (bytes : ByteArray) (start stop : Nat) (required : Bool) :
    validPort bytes start stop required = true ↔ PortGrammar bytes start stop required := by
  by_cases he : start = stop
  · simp [validPort, PortGrammar, he]
  · by_cases hs : start < stop
    · simp only [validPort, beq_iff_eq, he, ite_false, Bool.and_eq_true, Bool.or_eq_true,
        Bool.not_eq_true', decide_eq_true_eq, hs, true_and,
        spanEnd_eq_stop_iff bytes (start + 1) stop _ (by omega), PortGrammar, false_and, false_or,
        and_assoc, decimalOctet_iff]
    · simp [validPort, PortGrammar, he, hs]

def RegNameGrammar (bytes : ByteArray) (start stop : Nat) : Prop :=
  start ≤ stop ∧ stop ≤ bytes.size ∧ URIGrammar bytes RegNameOctet start stop

theorem regName_iff (bytes : ByteArray) (start stop : Nat) :
    uriComponent bytes start stop (fun b => unreserved b || subDelimiter b) = true ↔
      RegNameGrammar bytes start stop := by
  rw [uriComponent_iff]
  have h : (fun b => (unreserved b || subDelimiter b) = true) = RegNameOctet := by
    funext b; exact propext (regNameOctet_iff b)
  rw [h]; rfl

/-- Every wire byte in a URI atom satisfies any property shared by literals,
percent signs and hexadecimal digits. This includes delimiter exclusion. -/
theorem uriGrammar_octets (bytes : ByteArray) (literal p : UInt8 → Prop) (start stop : Nat)
    (h : URIGrammar bytes literal start stop) (hl : ∀ b, literal b → p b)
    (hp : p 37) (hx : ∀ b, HexOctet b → p b) : Octets bytes p start stop := by
  induction h with
  | empty i => intro j hj hk; omega
  | @char i stop hi hn hc tail ih =>
    intro j hj hk
    by_cases he : j = i
    · subst j; exact hl _ hc
    · exact ih j (by omega) hk
  | @escaped i stop hi he ha hb tail ih =>
    intro j hj hk
    by_cases h0 : j = i
    · subst j; simpa [he] using hp
    by_cases h1 : j = i + 1
    · subst j; exact hx _ ha
    by_cases h2 : j = i + 2
    · subst j; exact hx _ hb
    exact ih j (by omega) hk

theorem regName_no_delimiters (bytes : ByteArray) (start stop : Nat)
    (h : RegNameGrammar bytes start stop) :
    Octets bytes (fun b => b ≠ 58 ∧ b ≠ 91) start stop := by
  refine uriGrammar_octets bytes RegNameOctet (fun b => b ≠ 58 ∧ b ≠ 91) start stop h.2.2 ?_ ?_ ?_
  · intro b hb
    simp [RegNameOctet, ← UInt8.toNat_inj] at * <;> omega
  · decide
  · intro b hb
    simp [HexOctet, ← UInt8.toNat_inj] at * <;> omega

/-- A complete Host/authority: either a reg-name or a bracketed IP literal,
followed by the independently specified port suffix. All split points are grammar
witnesses; no parser result is assumed by this specification. -/
def AuthorityGrammar (bytes : ByteArray) (start stop : Nat) (connect : Bool) : Prop :=
  start ≤ stop ∧ stop ≤ bytes.size ∧ ∃ hostEnd,
    ((RegNameGrammar bytes start hostEnd ∧ (connect = false ∨ start < hostEnd)) ∨
      (∃ close, start < close ∧ close < stop ∧ bytes[start]! = 91 ∧
        bytes[close]! = 93 ∧ IPLiteralGrammar bytes (start + 1) close ∧ hostEnd = close + 1)) ∧
    PortGrammar bytes hostEnd stop connect

theorem validAuthority_sound (bytes : ByteArray) (start stop : Nat) (connect : Bool)
    (h : validAuthority bytes start stop connect = true) : AuthorityGrammar bytes start stop connect := by
  unfold validAuthority at h
  split at h
  · rename_i hb
    have bounds : start ≤ stop ∧ stop ≤ bytes.size := by simpa using hb
    split at h
    · rename_i ho
      have opening : start < stop ∧ bytes[start]! = 91 := by simpa using ho
      have scan := spanEnd_spec bytes stop (fun b => b != 93) (start + 1) (by omega)
      have hh : spanEnd bytes stop (fun b => b != 93) (start + 1) < stop ∧
          validIPLiteral bytes (start + 1) (spanEnd bytes stop (fun b => b != 93) (start + 1)) = true ∧
          validPort bytes (spanEnd bytes stop (fun b => b != 93) (start + 1) + 1) stop connect = true := by
        simpa [and_assoc] using h
      have close : bytes[spanEnd bytes stop (fun b => b != 93) (start + 1)]! = 93 := by
        rcases scan.2.2.2 with he | he
        · omega
        · simpa using he
      refine ⟨bounds.1, bounds.2, _, Or.inr ⟨_, by omega, hh.1, opening.2, close,
        (validIPLiteral_iff _ _ _).mp hh.2.1, rfl⟩, (validPort_iff _ _ _ _).mp hh.2.2⟩
    · have hh : (connect = false ∨ start < spanEnd bytes stop (fun b => b != 58) start) ∧
          uriComponent bytes start (spanEnd bytes stop (fun b => b != 58) start)
            (fun b => unreserved b || subDelimiter b) = true ∧
          validPort bytes (spanEnd bytes stop (fun b => b != 58) start) stop connect = true := by
        simpa [and_assoc] using h
      exact ⟨bounds.1, bounds.2, _, Or.inl ⟨(regName_iff _ _ _).mp hh.2.1, hh.1⟩,
        (validPort_iff _ _ _ _).mp hh.2.2⟩
  · contradiction

theorem validAuthority_complete (bytes : ByteArray) (start stop : Nat) (connect : Bool)
    (h : AuthorityGrammar bytes start stop connect) : validAuthority bytes start stop connect = true := by
  obtain ⟨hs, hb, hostEnd, host, port⟩ := h
  have hp := (validPort_iff bytes hostEnd stop connect).mpr port
  rcases host with ⟨reg, nonempty⟩ | ⟨close, hc, he, opening, closing, literal, rfl⟩
  · have regStart := reg.1
    have chars := regName_no_delimiters bytes start hostEnd reg
    have hEnd : hostEnd ≤ stop := by rcases port with p | p <;> omega
    have delimiter : hostEnd = stop ∨ (bytes[hostEnd]! != 58) = false := by
      rcases port with p | p
      · exact Or.inl p.1
      · exact Or.inr (by simp [p.2.1])
    have scan := spanEnd_complete bytes stop (fun b => b != 58) start hostEnd reg.1 hEnd
      (fun i hi hj => by simpa using (chars i hi hj).1) delimiter
    have notBracket : ¬ (start < stop ∧ bytes[start]! = 91) := by
      intro h
      by_cases empty : start = hostEnd
      · rcases port with p | p
        · omega
        · have : bytes[start]! = 58 := by simpa [empty] using p.2.1
          simp_all
      · exact (chars start (by omega) (by omega)).2 h.2
    have hr := (regName_iff _ _ _).mpr reg
    simp [validAuthority, hs, hb, notBracket, scan, nonempty, hr, hp]
  · have scan := spanEnd_complete bytes stop (fun b => b != 93) (start + 1) close
      (by omega) (by omega) (fun i hi hj => by simpa using literal.2.2.1 i hi hj)
      (Or.inr (by simp [closing]))
    have hl := (validIPLiteral_iff _ _ _).mpr literal
    simp [validAuthority, hs, hb, show start < stop by omega, opening, scan, he, hl, hp,
      -getElem!_pos]

/-- Exact authority grammar equivalence for every byte buffer and every interval,
including empty reg-names/ports, compressed IPv6, IPvFuture and CONNECT policy. -/
theorem validAuthority_iff (bytes : ByteArray) (start stop : Nat) (connect : Bool) :
    validAuthority bytes start stop connect = true ↔ AuthorityGrammar bytes start stop connect :=
  ⟨validAuthority_sound bytes start stop connect, validAuthority_complete bytes start stop connect⟩

end FastHTTP.Protocol
