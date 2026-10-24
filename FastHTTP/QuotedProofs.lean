import FastHTTP.LexicalProofs

namespace FastHTTP.Protocol

/-- RFC 9110 qdtext, independently specified using ASCII/obs-text intervals. -/
def QuoteText (b : UInt8) : Prop :=
  b.toNat = 9 ∨ b.toNat = 32 ∨ b.toNat = 33 ∨ (35 ≤ b.toNat ∧ b.toNat ≤ 91) ∨
    (93 ≤ b.toNat ∧ b.toNat ≤ 126) ∨ (128 ≤ b.toNat ∧ b.toNat ≤ 255)

theorem quoteText_iff (b : UInt8) : quoteText b = true ↔ QuoteText b := by
  have bound := b.toNat_lt
  simp [quoteText, fieldOctet, QuoteText, UInt8.le_iff_toNat_le, UInt8.toNat_ofNat, ← UInt8.toNat_inj] <;> omega

/-- RFC quoted-string body: qdtext or backslash + HTAB/SP/VCHAR/obs-text,
terminated by a literal double quote. The exact end cursor is part of the grammar. -/
inductive QuotedTailGrammar (bytes : ByteArray) (stop : Nat) : Nat → Nat → Prop where
  | close {i : Nat} : i < stop → bytes[i]! = 34 → QuotedTailGrammar bytes stop i (i + 1)
  | text {i last : Nat} : i < stop → QuoteText bytes[i]! →
      QuotedTailGrammar bytes stop (i + 1) last → QuotedTailGrammar bytes stop i last
  | escaped {i last : Nat} : i + 1 < stop → bytes[i]! = 92 → FieldOctet bytes[i + 1]! →
      QuotedTailGrammar bytes stop (i + 2) last → QuotedTailGrammar bytes stop i last

theorem quotedTail_sound (bytes : ByteArray) (stop i last : Nat)
    (h : quotedTail bytes stop i = some last) : QuotedTailGrammar bytes stop i last := by
  rw [quotedTail] at h
  split at h
  next hi =>
    dsimp only at h
    split at h
    next hquote =>
      cases h
      exact .close hi (by simpa using hquote)
    next hnquote =>
      split at h
      next hslash =>
        split at h
        next hnext =>
          have hn : i + 1 < stop ∧ fieldOctet bytes[i + 1]! = true := by simpa using hnext
          exact .escaped hn.1 (by simpa using hslash) ((fieldOctet_iff _).mp hn.2)
            (quotedTail_sound bytes stop (i + 2) last h)
        next hn => contradiction
      next hnslash =>
        split at h
        next htext =>
          exact .text hi ((quoteText_iff _).mp htext) (quotedTail_sound bytes stop (i + 1) last h)
        next hn => contradiction
  next hi => contradiction
termination_by stop - i
decreasing_by all_goals simp_all; omega

theorem quotedTail_complete (bytes : ByteArray) (stop i last : Nat)
    (h : QuotedTailGrammar bytes stop i last) : quotedTail bytes stop i = some last := by
  induction h with
  | close hi hb => rw [quotedTail]; simp [hi, hb]
  | @text i last hi ht tail ih =>
    have hb := (quoteText_iff _).mpr ht
    have chars : fieldOctet bytes[i]! = true ∧ bytes[i]! ≠ 34 ∧ bytes[i]! ≠ 92 := by
      simpa [quoteText, and_assoc] using hb
    rw [quotedTail]
    simp [hi, chars.2.1, chars.2.2, hb, ih]
  | @escaped i last hi hb hf tail ih =>
    rw [quotedTail]
    have hfield := (fieldOctet_iff _).mpr hf
    have hi' : i < stop := by omega
    simp [hi', hi, hb, hfield, ih]

theorem quotedTail_bounds (bytes : ByteArray) (stop i last : Nat)
    (h : QuotedTailGrammar bytes stop i last) : i < last ∧ last ≤ stop := by
  induction h <;> omega

def QuotedGrammar (bytes : ByteArray) (start stop last : Nat) : Prop :=
  start < stop ∧ stop ≤ bytes.size ∧ bytes[start]! = 34 ∧ QuotedTailGrammar bytes stop (start + 1) last

/-- Soundness and completeness of the production quoted-string parser,
including escapes, obs-text, all invalid controls, missing quotes and the cursor. -/
theorem quotedEnd_iff (bytes : ByteArray) (start stop last : Nat) :
    quotedEnd bytes start stop = some last ↔ QuotedGrammar bytes start stop last := by
  unfold quotedEnd QuotedGrammar
  split
  next h =>
    have hb : start < stop ∧ stop ≤ bytes.size ∧ bytes[start]! = 34 := by simpa [and_assoc] using h
    simp only [hb.1, hb.2.1, hb.2.2, true_and]
    exact ⟨quotedTail_sound bytes stop (start + 1) last, quotedTail_complete bytes stop (start + 1) last⟩
  next h =>
    constructor
    · intro impossible; contradiction
    · rintro ⟨hi, hs, hb, _⟩
      exact False.elim (h (by simp [hi, hs, hb]))

end FastHTTP.Protocol
