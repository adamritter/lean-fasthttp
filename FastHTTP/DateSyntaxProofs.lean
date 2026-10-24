import FastHTTP.DateSyntax

namespace FastHTTP.Protocol

theorem dateNumber_iff (bytes : ByteArray) (first last low high : Nat) :
    dateNumber bytes first last low high = true ↔ DateNumberGrammar bytes first last low high := by
  unfold DateNumberGrammar
  simp only [←decimal_iff]
  cases parsed : decimal bytes first last high <;> simp [dateNumber, parsed]

theorem validDateHeader_iff (bytes : ByteArray) :
    validDateHeader bytes = true ↔ DateHeaderGrammar bytes := by
  simp only [validDateHeader, DateHeaderGrammar, Bool.and_eq_true, beq_iff_eq,
    List.any_eq_true, equals_iff, dateNumber_iff, and_assoc]

end FastHTTP.Protocol
