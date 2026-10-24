import FastHTTP.Proofs

namespace FastHTTP.Protocol

/-- A finite alphabet for the literal CRLFCRLF grammar. All other octets have
identical delimiter semantics; the runtime still operates on the original bytes. -/
inductive DelimiterByte where
  | cr | lf | other
  deriving DecidableEq

def classifyDelimiterByte (b : UInt8) : DelimiterByte :=
  if b == 13 then .cr else if b == 10 then .lf else .other

/-- Independent specification: match the actual most recent wire symbols in
reverse order, not the parser's numeric DFA transition table. -/
def suffixCode : List DelimiterByte → Nat
  | .lf :: .cr :: .lf :: .cr :: _ => 4
  | .cr :: .lf :: .cr :: _ => 3
  | .lf :: .cr :: _ => 2
  | .cr :: _ => 1
  | _ => 0

def historyState (rev : List DelimiterByte) : ScanState :=
  { matched := suffixCode rev, count := rev.length,
    stop := if suffixCode rev == 4 then some rev.length else none }

set_option maxHeartbeats 2000000 in
/-- One DFA step agrees with literal suffix matching whenever scanning is active. -/
theorem scanByte_history (limit : Nat) (rev : List DelimiterByte) (b : UInt8)
    (h : suffixCode rev ≠ 4) (hl : rev.length < limit) :
    scanByte limit (historyState rev) b = historyState (classifyDelimiterByte b :: rev) := by
  have hn : ¬ rev.length >= limit := by omega
  by_cases h13 : b = 13 <;> by_cases h10 : b = 10 <;>
    simp_all only [classifyDelimiterByte, beq_iff_eq, ite_true, ite_false]
  all_goals cases rev with
  | nil => simp_all [historyState, suffixCode, scanByte]
  | cons a as =>
    cases as with
    | nil => cases a <;> simp_all [historyState, suffixCode, scanByte]
    | cons c cs =>
      cases cs with
      | nil => cases a <;> cases c <;> simp_all [historyState, suffixCode, scanByte]
      | cons d ds =>
        cases ds with
        | nil => cases a <;> cases c <;> cases d <;> simp_all [historyState, suffixCode, scanByte]
        | cons e es =>
          cases a <;> cases c <;> cases d <;> cases e <;>
            simp_all [historyState, suffixCode, scanByte]

/-- Literal search specification: stop at the first CRLFCRLF suffix, reject
before consuming any octet beyond the limit, otherwise request more input. -/
def referenceScan (limit : Nat) (rev : List DelimiterByte) (input : List UInt8) : ScanState :=
  if suffixCode rev == 4 then historyState rev
  else match input with
    | [] => historyState rev
    | b :: rest =>
      if rev.length >= limit then { historyState rev with invalid := true }
      else referenceScan limit (classifyDelimiterByte b :: rev) rest

theorem scanList_reference (limit : Nat) (rev : List DelimiterByte) (input : List UInt8) :
    input.foldl (scanByte limit) (historyState rev) = referenceScan limit rev input := by
  induction input generalizing rev with
  | nil => simp [referenceScan]
  | cons b rest ih =>
    by_cases h : suffixCode rev = 4
    · have ha : ((historyState rev).stop.isSome || (historyState rev).invalid) = true := by
        simp [historyState, h]
      rw [scanList_absorbed limit _ _ ha]
      simp [referenceScan, h]
    · by_cases hl : rev.length < limit
      · rw [List.foldl_cons, scanByte_history limit rev b h hl, ih]
        simp [referenceScan, h, Nat.not_le_of_gt hl]
      · have hn : rev.length >= limit := by omega
        have hs : scanByte limit (historyState rev) b = { historyState rev with invalid := true } := by
          simp [scanByte, historyState, h, hn]
        rw [List.foldl_cons, hs, scanList_absorbed limit _ _ (by simp)]
        simp [referenceScan, h, hn]

/-- Complete correspondence of the actual early-exit scanner to the literal
first-delimiter/limit specification for every byte buffer, including hostile input. -/
theorem scanFeedFast_reference (limit : Nat) (bytes : ByteArray) :
    scanFeedFast limit {} bytes = referenceScan limit [] bytes.data.toList := by
  rw [scanFeedFast_eq_scanFeed]
  unfold scanFeed
  rw [← Array.foldl_toList]
  exact scanList_reference limit [] bytes.data.toList

theorem classify_cr_iff (b : UInt8) : classifyDelimiterByte b = .cr ↔ b = 13 := by
  by_cases h13 : b = 13 <;> by_cases h10 : b = 10 <;> simp_all [classifyDelimiterByte]

theorem classify_lf_iff (b : UInt8) : classifyDelimiterByte b = .lf ↔ b = 10 := by
  by_cases h13 : b = 13 <;> by_cases h10 : b = 10 <;> simp_all [classifyDelimiterByte]

end FastHTTP.Protocol
