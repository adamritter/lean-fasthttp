import FastHTTP.Stream
import FastHTTP.NumericProofs
import FastHTTP.SyntaxProofs
import Init.Data.Nat.ToString
import Init.Data.String.Basic

namespace FastHTTP.Protocol

def numeralBytes (base n : Nat) : ByteArray :=
  (String.ofList (Nat.toDigits base n)).toUTF8

def numeralValue (base : Nat) (bytes : ByteArray) : Nat :=
  bytes.data.toList.foldl (fun n b => n * base + hexValue b) 0

theorem hexValue_iff (b : UInt8) : hexValue b < 16 ↔ HexOctet b := by
  have bound := b.toNat_lt
  simp only [hexValue, lower, HexOctet]
  repeat' split
  all_goals simp_all [UInt8.le_iff_toNat_le, UInt8.toNat_ofNat, UInt8.toNat_add] <;> omega

theorem digitChar_hex (n : Nat) (h : n < 16) :
    n.digitChar.utf8Size = 1 ∧ hexValue (UInt8.ofNat n.digitChar.toNat) = n := by
  match n with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 => decide
  | _ + 16 => omega

theorem digitChar_decimal (n : Nat) (h : n < 10) :
    DecimalOctet (UInt8.ofNat n.digitChar.toNat) ∧
      (UInt8.ofNat n.digitChar.toNat).toNat - 48 = n := by
  match n with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => unfold DecimalOctet; decide
  | _ + 10 => omega

/-- UTF-8 is byte-for-byte ASCII for the numeral alphabet; character counts
cannot silently replace wire octet counts in this proof. -/
theorem numeral_single_byte (cs : List Char) (h : ∀ c ∈ cs, c.utf8Size = 1) :
    (String.ofList cs).toUTF8.data.toList = cs.map (fun c => UInt8.ofNat c.toNat) := by
  simp only [String.toUTF8_eq_toByteArray, String.toByteArray_ofList]
  induction cs with
  | nil => simp
  | cons c cs ih =>
    rw [List.utf8Encode_cons, List.utf8Encode_singleton, String.utf8EncodeChar_eq_singleton (h c (by simp))]
    simp [ih (fun c hc => h c (by simp [hc]))]
    change c.val.toUInt8 = UInt8.ofNat c.val.toNat
    symm
    exact UInt8.ofNat_uInt32ToNat c.val

/-- Every emitted digit has its stated value and belongs to the base's alphabet. -/
theorem numeral_alphabet (base n : Nat) (hb : 1 < base) (hmax : base ≤ 16) :
    ∀ c ∈ Nat.toDigits base n,
      c.utf8Size = 1 ∧ hexValue (UInt8.ofNat c.toNat) < base := by
  induction n using Nat.base_induction base hb with
  | single n hn =>
    intro c hc
    simp only [Nat.toDigits_of_lt_base hn, List.mem_singleton] at hc
    subst c
    have digit := digitChar_hex n (by omega)
    exact ⟨digit.1, by rw [digit.2]; exact hn⟩
  | digit n k hk hn ih =>
    rw [← Nat.toDigits_append_toDigits hb hn hk, Nat.toDigits_of_lt_base hk]
    intro c hc
    simp only [List.mem_append, List.mem_singleton] at hc
    rcases hc with hc | rfl
    · exact ih c hc
    · have digit := digitChar_hex k (by omega)
      exact ⟨digit.1, by rw [digit.2]; exact hk⟩

/-- Positional value of the actual formatted digits, for arbitrary natural
numbers and bases 2..16. There is no fixed machine-word size assumption. -/
theorem numeral_roundtrip (base n : Nat) (hb : 1 < base) (hmax : base ≤ 16) :
    numeralValue base (numeralBytes base n) = n := by
  unfold numeralValue numeralBytes
  rw [numeral_single_byte _ (fun c hc => (numeral_alphabet base n hb hmax c hc).1)]
  simp only [List.foldl_map]
  induction n using Nat.base_induction base hb with
  | single n hn =>
    rw [Nat.toDigits_of_lt_base hn]
    simp [digitChar_hex n (by omega)]
  | digit n k hk hn ih =>
    rw [← Nat.toDigits_append_toDigits hb hn hk, Nat.toDigits_of_lt_base hk, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, ih, (digitChar_hex k (by omega)).2]
    simp only [Nat.mul_comm]

/-- Decimal output is an actual RFC DIGIT sequence with the exact numeric value. -/
theorem decimal_wire_encoding (n : Nat) :
    DecimalEncoding (toString n).toUTF8.data.toList n := by
  rw [Nat.toString_eq_ofList_toDigits,
    numeral_single_byte _ (fun c hc => (numeral_alphabet 10 n (by omega) (by omega) c hc).1)]
  refine ⟨by simp, ?_, ?_⟩
  · have digits : ∀ m : Nat, ∀ c ∈ Nat.toDigits 10 m, DecimalOctet (UInt8.ofNat c.toNat) := by
      intro m
      induction m using Nat.base_induction 10 (by omega) with
      | single m hm =>
        intro c hc
        simp only [Nat.toDigits_of_lt_base hm, List.mem_singleton] at hc
        subst c
        exact (digitChar_decimal m hm).1
      | digit m k hk hm ih =>
        rw [← Nat.toDigits_append_toDigits (by omega) hm hk, Nat.toDigits_of_lt_base hk]
        intro c hc
        simp only [List.mem_append, List.mem_singleton] at hc
        rcases hc with hc | rfl
        · exact ih c hc
        · exact (digitChar_decimal k hk).1
    intro b hb
    rcases List.mem_map.mp hb with ⟨c, hc, rfl⟩
    exact digits n c hc
  · unfold decimalValue
    rw [List.foldl_map]
    induction n using Nat.base_induction 10 (by omega) with
    | single n hn =>
      rw [Nat.toDigits_of_lt_base hn]
      simp only [List.foldl_cons, List.foldl_nil, Nat.zero_mul, Nat.zero_add]
      exact (digitChar_decimal n hn).2
    | digit n k hk hn ih =>
      rw [← Nat.toDigits_append_toDigits (by omega) hn hk, Nat.toDigits_of_lt_base hk, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, (digitChar_decimal k hk).2]
      simpa only [Nat.mul_comm] using congrArg (fun x => x * 10 + k) ih

/-- The production Content-Length parser decodes every decimal value emitted by
the response formatter, for every limit large enough to represent that value. -/
theorem decimal_wire_roundtrip (n limit : Nat) (hlimit : n ≤ limit) :
    decimal (toString n).toUTF8 0 (toString n).toUTF8.size limit = some n := by
  apply (decimal_iff _ _ _ _ _).mpr
  have encoding := decimal_wire_encoding n
  refine ⟨?_, by omega, ?_, hlimit⟩
  · have hn := encoding.1
    have := List.length_pos_iff.mpr hn
    simpa using this
  · rw [ByteArray.extract_zero_size]
    exact encoding

/-- Chunk output is exactly hexadecimal length + CRLF, the original binary
payload and CRLF. The independently evaluated numeral equals ByteArray.size. -/
theorem encodeChunk_wire (bytes : ByteArray) :
    encodeChunk bytes = #[numeralBytes 16 bytes.size ++ "\r\n".toUTF8, bytes, "\r\n".toUTF8] ∧
      numeralValue 16 (numeralBytes 16 bytes.size) = bytes.size := by
  constructor
  · simp [encodeChunk, numeralBytes, String.toByteArray_append]
  · exact numeral_roundtrip 16 bytes.size (by omega) (by omega)

end FastHTTP.Protocol
