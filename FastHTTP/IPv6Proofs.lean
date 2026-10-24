import FastHTTP.NumericProofs
import FastHTTP.SyntaxProofs

namespace FastHTTP.Protocol

/-- The five RFC 3986 dec-octet productions, stated with ASCII intervals. -/
inductive DecOctetGrammar : List UInt8 → Prop where
  | one (a : UInt8) : DecimalOctet a → DecOctetGrammar [a]
  | two (a b : UInt8) : 49 ≤ a.toNat → a.toNat ≤ 57 → DecimalOctet b → DecOctetGrammar [a,b]
  | hundred (a b c : UInt8) : a.toNat = 49 → DecimalOctet b → DecimalOctet c → DecOctetGrammar [a,b,c]
  | twoHundred (a b c : UInt8) : a.toNat = 50 → 48 ≤ b.toNat → b.toNat ≤ 52 →
      DecimalOctet c → DecOctetGrammar [a,b,c]
  | last (a b c : UInt8) : a.toNat = 50 → b.toNat = 53 → 48 ≤ c.toNat → c.toNat ≤ 53 →
      DecOctetGrammar [a,b,c]

theorem validDecOctet_sound (xs : List UInt8) (h : validDecOctet xs = true) : DecOctetGrammar xs := by
  unfold validDecOctet at h
  split at h
  · rename_i a
    exact .one a (by simpa [DecimalOctet, UInt8.le_iff_toNat_le] using h)
  · rename_i a b
    have hh : 49 ≤ a.toNat ∧ a.toNat ≤ 57 ∧ DecimalOctet b := by
      simpa [DecimalOctet, UInt8.le_iff_toNat_le, and_assoc] using h
    exact .two a b hh.1 hh.2.1 hh.2.2
  · rename_i a b c
    have hh : (a.toNat = 49 ∧ DecimalOctet b ∧ DecimalOctet c) ∨
        (a.toNat = 50 ∧ 48 ≤ b.toNat ∧ b.toNat ≤ 52 ∧ DecimalOctet c) ∨
        (a.toNat = 50 ∧ b.toNat = 53 ∧ 48 ≤ c.toNat ∧ c.toNat ≤ 53) := by
      simpa [DecimalOctet, UInt8.le_iff_toNat_le, ← UInt8.toNat_inj, and_assoc, or_assoc] using h
    rcases hh with hh | hh | hh
    · exact .hundred a b c hh.1 hh.2.1 hh.2.2
    · exact .twoHundred a b c hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
    · exact .last a b c hh.1 hh.2.1 hh.2.2.1 hh.2.2.2
  · contradiction

theorem validDecOctet_complete (xs : List UInt8) (h : DecOctetGrammar xs) : validDecOctet xs = true := by
  cases h <;> simp_all [validDecOctet, DecimalOctet, UInt8.le_iff_toNat_le, ← UInt8.toNat_inj] <;> omega

theorem validDecOctet_iff (xs : List UInt8) : validDecOctet xs = true ↔ DecOctetGrammar xs :=
  ⟨validDecOctet_sound xs, validDecOctet_complete xs⟩

/-- Four decimal octets separated by literal dots. -/
def IPv4Grammar (s : String) : Prop :=
  (s.splitOn ".").length = 4 ∧ ∀ p ∈ s.splitOn ".", DecOctetGrammar p.toUTF8.data.toList

theorem validIPv4_iff (s : String) : validIPv4 s = true ↔ IPv4Grammar s := by
  simp [validIPv4, IPv4Grammar, validDecOctet_iff]

/-- One to four hexadecimal ASCII octets in a colon-delimited group. The absence
of a dot spells out the literal delimiter distinction from the final IPv4 form. -/
def H16Grammar (s : String) : Prop :=
  s.contains '.' = false ∧ 0 < s.utf8ByteSize ∧ s.utf8ByteSize ≤ 4 ∧
    ∀ b ∈ s.toUTF8.data.toList, HexOctet b

theorem validH16_iff (s : String) : validH16 s = true ↔
    0 < s.utf8ByteSize ∧ s.utf8ByteSize ≤ 4 ∧ ∀ b ∈ s.toUTF8.data.toList, HexOctet b := by
  simp only [validH16, Bool.and_eq_true, decide_eq_true_eq, Array.all_eq_true',
    Array.mem_toList_iff, hexDigit_iff, and_assoc]

/-- An IPv4 tail accounts for two 16-bit groups and must be the final component.
All preceding pieces are h16; the count is mathematical and unbounded. -/
inductive IPv6PartsGrammar (ipv4 : Bool) : List String → Nat → Prop where
  | nil : IPv6PartsGrammar ipv4 [] 0
  | hex {p : String} {rest : List String} {n : Nat} : H16Grammar p →
      IPv6PartsGrammar ipv4 rest n → IPv6PartsGrammar ipv4 (p :: rest) (n + 1)
  | tail {p : String} : ipv4 = true → p.contains '.' = true → IPv4Grammar p →
      IPv6PartsGrammar ipv4 [p] 2

theorem ipv6Parts_sound (parts : List String) (ipv4 : Bool) (n : Nat)
    (h : ipv6Parts parts ipv4 = some n) : IPv6PartsGrammar ipv4 parts n := by
  induction parts generalizing n with
  | nil => simp [ipv6Parts] at h; subst n; exact .nil
  | cons p rest ih =>
    simp only [ipv6Parts] at h
    split at h
    · rename_i hd
      split at h
      · rename_i hv
        have hh : ipv4 = true ∧ rest = [] ∧ validIPv4 p = true := by simpa [and_assoc] using hv
        obtain ⟨hi, rfl, hvalid⟩ := hh
        cases h
        exact .tail hi hd ((validIPv4_iff _).mp hvalid)
      · contradiction
    · rename_i hd
      split at h
      · rename_i hx
        have hg : H16Grammar p := ⟨Bool.eq_false_iff.mpr hd, (validH16_iff p).mp hx⟩
        cases ht : ipv6Parts rest ipv4 with
        | none => simp [ht] at h
        | some m =>
          simp only [ht, Option.map_some, Option.some.injEq] at h
          subst n
          exact .hex hg (ih m ht)
      · contradiction

theorem ipv6Parts_complete (parts : List String) (ipv4 : Bool) (n : Nat)
    (h : IPv6PartsGrammar ipv4 parts n) : ipv6Parts parts ipv4 = some n := by
  induction h with
  | nil => rfl
  | @hex p rest n hg tail ih =>
    have hh : validH16 p = true := (validH16_iff p).mpr hg.2
    simp [ipv6Parts, hg.1, hh, ih]
  | tail hi hd hg => simp [ipv6Parts, hi, hd, (validIPv4_iff _).mpr hg]

theorem ipv6Parts_iff (parts : List String) (ipv4 : Bool) (n : Nat) :
    ipv6Parts parts ipv4 = some n ↔ IPv6PartsGrammar ipv4 parts n :=
  ⟨ipv6Parts_sound parts ipv4 n, ipv6Parts_complete parts ipv4 n⟩

/-- Empty sides of :: have zero groups; nonempty sides are colon-separated. -/
def IPv6GroupsGrammar (s : String) (ipv4 : Bool) (n : Nat) : Prop :=
  (s.isEmpty = true ∧ n = 0) ∨ (s.isEmpty = false ∧ IPv6PartsGrammar ipv4 (s.splitOn ":") n)

theorem ipv6Groups_iff (s : String) (ipv4 : Bool) (n : Nat) :
    ipv6Groups s ipv4 = some n ↔ IPv6GroupsGrammar s ipv4 n := by
  unfold ipv6Groups IPv6GroupsGrammar
  cases hs : s.isEmpty with
  | false => simp [ipv6Parts_iff]
  | true => simp [eq_comm]

/-- RFC 3986's eight 16-bit pieces, with an optional single :: eliding at least
one piece. Literal delimiter splitting excludes extra compression markers;
embedded IPv4 is admitted only in the final two pieces. -/
def IPv6Grammar (s : String) : Prop :=
  (∃ whole, s.splitOn "::" = [whole] ∧ IPv6GroupsGrammar whole true 8) ∨
  (∃ left right a b, s.splitOn "::" = [left, right] ∧
    IPv6GroupsGrammar left false a ∧ IPv6GroupsGrammar right true b ∧ a + b < 8)

/-- Exact equivalence of the production IPv6 validator and the independent
counted-group grammar, including compressed and final-IPv4 forms. -/
theorem validIPv6_iff (s : String) : validIPv6 s = true ↔ IPv6Grammar s := by
  unfold validIPv6 IPv6Grammar
  cases hs : s.splitOn "::" with
  | nil => simp
  | cons first rest =>
    cases rest with
    | nil => simp [← ipv6Groups_iff]
    | cons second tail =>
      cases tail with
      | nil =>
        cases ha : ipv6Groups first false <;> cases hb : ipv6Groups second true <;>
          simp [← ipv6Groups_iff, ha, hb, and_assoc]
      | cons third more => simp

/-- RFC dec-octet's positional numeric value is always within one octet. -/
theorem decOctet_value_bound (xs : List UInt8) (h : DecOctetGrammar xs) : decimalValue xs ≤ 255 := by
  cases h <;> simp_all [decimalValue, DecimalOctet] <;> omega

theorem utf8IPv6_iff (bytes : ByteArray) : utf8IPv6 bytes = true ↔
    ∃ text, String.fromUTF8? bytes = some text ∧ IPv6Grammar text := by
  unfold utf8IPv6
  cases h : String.fromUTF8? bytes <;> simp [validIPv6_iff]

theorem invalid_utf8_ipv6_rejected (bytes : ByteArray) (h : String.fromUTF8? bytes = none) :
    utf8IPv6 bytes = false := by simp [utf8IPv6, h]

end FastHTTP.Protocol
