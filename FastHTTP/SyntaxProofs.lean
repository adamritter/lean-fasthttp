import FastHTTP.Syntax
import Std.Tactic

namespace FastHTTP.Protocol

/-- The RFC 3986 HEXDIG terminal, independently stated as ASCII intervals. -/
def HexOctet (b : UInt8) : Prop :=
  (48 ≤ b.toNat ∧ b.toNat ≤ 57) ∨
  (65 ≤ b.toNat ∧ b.toNat ≤ 70) ∨ (97 ≤ b.toNat ∧ b.toNat ≤ 102)

/-- RFC 3986 unreserved / sub-delims / ':' / '@' / '/' / '?'.
Percent-encoding is a separate grammar production. -/
def PathOctet (b : UInt8) : Prop :=
  (65 ≤ b.toNat ∧ b.toNat ≤ 90) ∨ (97 ≤ b.toNat ∧ b.toNat ≤ 122) ∨
  (48 ≤ b.toNat ∧ b.toNat ≤ 57) ∨
  b.toNat ∈ [45,46,95,126,33,36,38,39,40,41,42,43,44,59,61,58,64,47,63]

theorem hexDigit_iff (b : UInt8) : hexDigit b = true ↔ HexOctet b := by
  simp only [hexDigit, HexOctet, lower, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq, UInt8.le_iff_toNat_le]
  split <;> simp_all [UInt8.toNat_ofNat, UInt8.toNat_add] <;> omega

theorem pathOctet_iff (b : UInt8) :
    (unreserved b || subDelimiter b || b == 58 || b == 64 || b == 47 || b == 63) = true ↔
      PathOctet b := by
  simp [unreserved, subDelimiter, PathOctet, UInt8.le_iff_toNat_le,
    UInt8.toNat_ofNat, ← UInt8.toNat_inj] <;> omega

/-- Independent URI component grammar over a wire interval. Each production
consumes one literal octet or exactly '%' HEXDIG HEXDIG; no normalization occurs.
The predicate is independent of the parser's recursion and Boolean conditions. -/
inductive URIGrammar (bytes : ByteArray) (literal : UInt8 → Prop) : Nat → Nat → Prop where
  | empty (i : Nat) : URIGrammar bytes literal i i
  | char {i stop : Nat} : i < stop → bytes[i]! ≠ 37 → literal bytes[i]! →
      URIGrammar bytes literal (i + 1) stop → URIGrammar bytes literal i stop
  | escaped {i stop : Nat} : i + 2 < stop → bytes[i]! = 37 →
      HexOctet bytes[i + 1]! → HexOctet bytes[i + 2]! →
      URIGrammar bytes literal (i + 3) stop → URIGrammar bytes literal i stop

/-- Syntax-directed completeness and soundness, for every allowed literal set. -/
theorem uriLoop_iff (bytes : ByteArray) (stop : Nat) (allowed : UInt8 → Bool)
    (i : Nat) (hi : i ≤ stop) :
    uriLoop bytes stop allowed i = true ↔ URIGrammar bytes (fun b => allowed b = true) i stop := by
  rw [uriLoop]
  split
  next h =>
    by_cases hp : bytes[i]! = 37
    · simp only [hp, beq_self_eq_true, ite_true, Bool.and_eq_true, decide_eq_true_eq]
      split
      next hh =>
        rw [uriLoop_iff bytes stop allowed (i + 3) (by omega)]
        constructor
        · intro tail
          exact .escaped hh.1.1 hp ((hexDigit_iff _).mp hh.1.2) ((hexDigit_iff _).mp hh.2) tail
        · intro grammar
          cases grammar with
          | empty => omega
          | char _ hn => contradiction
          | escaped _ _ _ _ tail => exact tail
      next hh =>
        constructor
        · intro impossible; contradiction
        · intro grammar
          cases grammar with
          | empty => omega
          | char _ hn => contradiction
          | escaped bound _ ha hb tail =>
            exact False.elim (hh ⟨⟨bound, (hexDigit_iff _).mpr ha⟩, (hexDigit_iff _).mpr hb⟩)
    · simp only [beq_iff_eq, hp, ite_false, Bool.and_eq_true]
      rw [uriLoop_iff bytes stop allowed (i + 1) (by omega)]
      constructor
      · rintro ⟨ha, tail⟩; exact .char h hp ha tail
      · intro grammar
        cases grammar with
        | empty => omega
        | char _ _ ha tail => exact ⟨ha, tail⟩
        | escaped _ he => contradiction
  next h =>
    have he : i = stop := by omega
    subst i
    exact ⟨fun _ => .empty stop, fun _ => rfl⟩
termination_by stop - i

theorem uriComponent_iff (bytes : ByteArray) (start stop : Nat) (allowed : UInt8 → Bool) :
    uriComponent bytes start stop allowed = true ↔
      start ≤ stop ∧ stop ≤ bytes.size ∧ URIGrammar bytes (fun b => allowed b = true) start stop := by
  simp only [uriComponent, Bool.and_eq_true, decide_eq_true_eq]
  by_cases h : start ≤ stop
  · rw [uriLoop_iff bytes stop allowed start h]; simp [and_assoc]
  · simp [h]

/-- The public path/query validator accepts exactly the RFC atom grammar. -/
theorem validPathQuery_iff (bytes : ByteArray) (start stop : Nat) :
    validPathQuery bytes start stop = true ↔
      start ≤ stop ∧ stop ≤ bytes.size ∧ URIGrammar bytes PathOctet start stop := by
  rw [validPathQuery, uriComponent_iff]
  have he : (fun b => (unreserved b || subDelimiter b || b == 58 || b == 64 || b == 47 || b == 63) = true) = PathOctet := by
    funext b
    exact propext (pathOctet_iff b)
  rw [he]

end FastHTTP.Protocol
