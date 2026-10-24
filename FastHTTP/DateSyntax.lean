import FastHTTP.TargetProofs
import FastHTTP.NumericProofs

namespace FastHTTP.Protocol

def httpWeekdays : List String := ["Mon", "Tue", "Wed", "Thu", "Fri", "Sat", "Sun"]
def httpMonths : List String := ["Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"]

def dateNumber (bytes : ByteArray) (first last low high : Nat) : Bool :=
  match decimal bytes first last high with
  | none => false
  | some n => low ≤ n

def DateNumberGrammar (bytes : ByteArray) (first last low high : Nat) : Prop :=
  ∃ n, (first < last ∧ last ≤ bytes.size ∧ DecimalEncoding (bytes.extract first last).data.toList n ∧ n ≤ high) ∧ low ≤ n

/-- Exact IMF-fixdate wire grammar, including its Date field name and the final
empty CRLF line. Bounds exclude non-ASCII digits, invalid widths and injection.
Clock accuracy/calendar interpretation is separate from this wire grammar. -/
def DateHeaderGrammar (bytes : ByteArray) : Prop :=
  bytes.size = 39 ∧ TextGrammar bytes 0 6 "Date: " ∧
  (∃ day ∈ httpWeekdays, TextGrammar bytes 6 9 day) ∧ TextGrammar bytes 9 11 ", " ∧
  DateNumberGrammar bytes 11 13 1 31 ∧ TextGrammar bytes 13 14 " " ∧
  (∃ month ∈ httpMonths, TextGrammar bytes 14 17 month) ∧ TextGrammar bytes 17 18 " " ∧
  DateNumberGrammar bytes 18 22 0 9999 ∧ TextGrammar bytes 22 23 " " ∧
  DateNumberGrammar bytes 23 25 0 23 ∧ TextGrammar bytes 25 26 ":" ∧
  DateNumberGrammar bytes 26 28 0 59 ∧ TextGrammar bytes 28 29 ":" ∧
  DateNumberGrammar bytes 29 31 0 60 ∧ TextGrammar bytes 31 39 " GMT\r\n\r\n"

def validDateHeader (bytes : ByteArray) : Bool :=
  bytes.size == 39 && equals bytes 0 6 "Date: " &&
  httpWeekdays.any (equals bytes 6 9 ·) && equals bytes 9 11 ", " &&
  dateNumber bytes 11 13 1 31 && equals bytes 13 14 " " &&
  httpMonths.any (equals bytes 14 17 ·) && equals bytes 17 18 " " &&
  dateNumber bytes 18 22 0 9999 && equals bytes 22 23 " " &&
  dateNumber bytes 23 25 0 23 && equals bytes 25 26 ":" &&
  dateNumber bytes 26 28 0 59 && equals bytes 28 29 ":" &&
  dateNumber bytes 29 31 0 60 && equals bytes 31 39 " GMT\r\n\r\n"

end FastHTTP.Protocol
