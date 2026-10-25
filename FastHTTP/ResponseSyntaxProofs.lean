import FastHTTP.ResponseSyntax

namespace FastHTTP.Protocol

theorem outputStringAll_iff (text : String) (p : UInt8 → Bool) (i : Nat) :
    outputStringAll text p i = true ↔ ∀ j, i ≤ j → (hj : j < text.utf8ByteSize) → p (text.getUTF8Byte ⟨j⟩ hj) = true := by
  rw [outputStringAll]
  split
  next hi =>
    rw [Bool.and_eq_true, outputStringAll_iff]
    constructor
    · rintro ⟨first, rest⟩ j hij hj
      by_cases eq : j = i
      · subst j; exact first
      · exact rest j (by omega) hj
    · intro all
      exact ⟨all i (by omega) hi, fun j hj h => all j (by omega) h⟩
  next hi =>
    constructor
    · intro _ j hij hj; omega
    · intro _; rfl
termination_by text.utf8ByteSize - i

theorem outputStringAll_eq_all (text : String) (p : UInt8 → Bool) :
    outputStringAll text p = text.toUTF8.data.all p := by
  apply Bool.eq_iff_iff.mpr
  rw [outputStringAll_iff, Array.all_eq_true']
  constructor
  · intro h b hb
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hb
    exact h i (by omega) hi
  · intro h i _ hi
    exact h _ (Array.getElem_mem hi)

theorem validOutputName_iff (name : String) : validOutputName name = true ↔ OutputNameGrammar name := by
  simp only [validOutputName, outputStringAll_eq_all, OutputNameGrammar, Bool.and_eq_true, decide_eq_true_eq,
    Array.all_eq_true', Array.mem_toList_iff, token_iff]

theorem outputValueOctet_iff (b : UInt8) :
    ((b >= 32 && b != 127) || b == 9) = true ↔ FieldOctet b := by
  have bound := b.toNat_lt
  simp [FieldOctet, UInt8.le_iff_toNat_le, UInt8.toNat_ofNat, ←UInt8.toNat_inj] <;> omega

theorem validFieldValue_iff (value : String) : validFieldValue value = true ↔ OutputValueGrammar value := by
  simp only [validFieldValue, outputStringAll_eq_all, OutputValueGrammar, Array.all_eq_true', Array.mem_toList_iff, outputValueOctet_iff]

theorem validOutputReason_iff (reason : String) : validOutputReason reason = true ↔ OutputReasonGrammar reason := by
  simp only [validOutputReason, outputStringAll_eq_all, OutputReasonGrammar, Bool.and_eq_true, decide_eq_true_eq,
    Array.all_eq_true', Array.mem_toList_iff, UInt8.le_iff_toNat_le, UInt8.lt_iff_toNat_lt, UInt8.toNat_ofNat]

theorem outputNameIs_iff (name target : String) : outputNameIs name target = true ↔
    TextGrammar name.toUTF8 0 name.utf8ByteSize target true := equals_iff _ _ _ _ _

theorem outputFieldAllowed_iff (managed seen : List String) (name : String) :
    outputFieldAllowed managed seen name = true ↔ OutputFieldPolicy managed seen name := by
  change (!(managed.any (outputNameIs name)) &&
    (outputNameIs name "set-cookie" || !(seen.any (outputNameIs name)))) = true ↔ _
  simp [OutputFieldPolicy, outputNameIs_iff]

end FastHTTP.Protocol
