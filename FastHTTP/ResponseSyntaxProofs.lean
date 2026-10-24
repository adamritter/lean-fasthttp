import FastHTTP.ResponseSyntax

namespace FastHTTP.Protocol

theorem validOutputName_iff (name : String) : validOutputName name = true ↔ OutputNameGrammar name := by
  simp only [validOutputName, OutputNameGrammar, Bool.and_eq_true, decide_eq_true_eq,
    Array.all_eq_true', Array.mem_toList_iff, token_iff]

theorem outputValueOctet_iff (b : UInt8) :
    ((b >= 32 && b != 127) || b == 9) = true ↔ FieldOctet b := by
  have bound := b.toNat_lt
  simp [FieldOctet, UInt8.le_iff_toNat_le, UInt8.toNat_ofNat, ←UInt8.toNat_inj] <;> omega

theorem validFieldValue_iff (value : String) : validFieldValue value = true ↔ OutputValueGrammar value := by
  simp only [validFieldValue, OutputValueGrammar, Array.all_eq_true', Array.mem_toList_iff, outputValueOctet_iff]

theorem validOutputReason_iff (reason : String) : validOutputReason reason = true ↔ OutputReasonGrammar reason := by
  simp only [validOutputReason, OutputReasonGrammar, Bool.and_eq_true, decide_eq_true_eq,
    Array.all_eq_true', Array.mem_toList_iff, UInt8.le_iff_toNat_le, UInt8.lt_iff_toNat_lt, UInt8.toNat_ofNat]

theorem outputNameIs_iff (name target : String) : outputNameIs name target = true ↔
    TextGrammar name.toUTF8 0 name.utf8ByteSize target true := equals_iff _ _ _ _ _

theorem outputFieldAllowed_iff (managed seen : List String) (name : String) :
    outputFieldAllowed managed seen name = true ↔ OutputFieldPolicy managed seen name := by
  simp [outputFieldAllowed, OutputFieldPolicy, List.any_eq_true, outputNameIs_iff]

end FastHTTP.Protocol
