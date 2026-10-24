import FastHTTP.HeaderSemanticsProofs

namespace FastHTTP.Protocol

/-- A complete field block with its accumulated meaning. Each constructor uses
independent field syntax and semantic value grammars, and retains field order. -/
inductive HeadersMeaning (cfg : Config) (bytes : ByteArray) (stop minor : Nat) :
    Nat → HeaderState → HeaderState → Prop where
  | empty {i : Nat} (state : HeaderState) :
      i + 2 = stop → bytes[i]! = 13 → bytes[i + 1]! = 10 →
      (minor = 0 ∨ state.host = true) → HeadersMeaning cfg bytes stop minor i state state
  | field (line : FieldLine) (initial next result : HeaderState) :
      FieldLineGrammar bytes stop line →
      HeaderFieldGrammar cfg bytes line.valueEnd minor
        { initial with line := line.start, colon := line.colon } next →
      HeadersMeaning cfg bytes stop minor line.next next result →
      HeadersMeaning cfg bytes stop minor line.start initial result

theorem parseHeaders_meaning_sound (cfg : Config) (bytes : ByteArray) (stop minor i : Nat)
    (initial result : HeaderState) (hs : 2 ≤ stop) (hb : stop ≤ bytes.size)
    (cr : bytes[stop - 2]! = 13) (lf : bytes[stop - 1]! = 10)
    (h : parseHeaders.loop cfg bytes stop minor i initial = .ok result) :
    HeadersMeaning cfg bytes stop minor i initial result := by
  rw [parseHeaders.loop] at h
  split at h
  next hi =>
    cases hp : parseFieldLine bytes i stop with
    | none => simp [hp] at h
    | some line =>
      simp only [hp] at h
      split at h
      · contradiction
      · rename_i progress
        split at h
        · contradiction
        · rename_i next parsed
          have grammar := parseFieldLine_sound bytes i stop line hp
          have bounds := grammar.2.bounds
          have value := grammar.2.valueBounds
          have start := grammar.2.valueStart
          have ending := grammar.2.next
          have field := (parseField_grammar_iff cfg bytes line.valueEnd stop minor
            { initial with line := i, colon := line.colon } next
            (by simp only; omega) (by simp only; omega) (by omega) hb grammar.2.lf).mp parsed
          have tail := parseHeaders_meaning_sound cfg bytes stop minor line.next next result hs hb cr lf h
          have result := HeadersMeaning.field line initial next result grammar.2 (by simpa [grammar.1] using field) tail
          simpa [grammar.1] using result
  next hi =>
    split at h
    · contradiction
    · rename_i guard
      have guardParts : i = stop - 2 ∧ ¬(minor ≠ 0 ∧ (!initial.host) = true) := by
        simpa only [Bool.or_eq_true, Bool.and_eq_true, not_or, bne_iff_ne, Decidable.not_not] using guard
      have pos := guardParts.1
      have host : minor = 0 ∨ initial.host = true := by
        simp only [Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, Bool.not_eq_true, not_or] at guard
        cases hh : initial.host <;> simp_all
      cases h
      exact .empty initial (by omega) (by simpa [pos] using cr)
        (by simpa [pos, show stop - 2 + 1 = stop - 1 by omega] using lf) host
termination_by stop - 2 - i

theorem parseHeaders_meaning_complete (cfg : Config) (bytes : ByteArray) (stop minor i : Nat)
    (initial result : HeaderState)
    (h : HeadersMeaning cfg bytes stop minor i initial result) :
    parseHeaders.loop cfg bytes stop minor i initial = .ok result := by
  induction h with
  | @empty i state ending cr lf host =>
      rw [parseHeaders.loop]
      have pos : i = stop - 2 := by omega
      have bound : ¬i < stop - 2 := by omega
      simp only [bound, ↓reduceIte, pos, bne_self_eq_false, Bool.false_or]
      rcases host with zero | present
      · simp [zero]
      · simp [present]
  | field line initial next result grammar meaning tail ih =>
      have bounds := grammar.bounds
      have start := grammar.valueStart
      have ending := grammar.next
      have vb := grammar.valueBounds
      have before : line.start < stop - 2 := by omega
      have progress : ¬line.next ≤ line.start := by omega
      have parsed := (parseField_grammar_iff cfg bytes line.valueEnd stop minor
        { initial with line := line.start, colon := line.colon } next
        bounds.1 (by simp only; omega) (by omega) bounds.2.2 grammar.lf).mpr meaning
      rw [parseHeaders.loop]
      simp only [before, ↓reduceIte, parseFieldLine_complete bytes stop line grammar, progress, parsed]
      exact ih

theorem parseHeaders_grammar_iff (cfg : Config) (bytes : ByteArray) (start stop minor : Nat)
    (result : HeaderState) (hs : 2 ≤ stop) (hb : stop ≤ bytes.size)
    (cr : bytes[stop - 2]! = 13) (lf : bytes[stop - 1]! = 10) :
    parseHeaders cfg bytes start stop minor = .ok result ↔
      HeadersMeaning cfg bytes stop minor start { line := start, colon := start } result :=
  ⟨parseHeaders_meaning_sound cfg bytes stop minor start _ result hs hb cr lf,
    parseHeaders_meaning_complete cfg bytes stop minor start _ result⟩

/-- RFC message-length precedence with the server's strict rejection of any
simultaneous Content-Length and Transfer-Encoding. -/
def FramingGrammar (length : Option Nat) (chunked : Bool) (result : Framing) : Prop :=
  (length = none ∧ chunked = true ∧ result = .chunked) ∨
  (chunked = false ∧ result = .fixed (length.getD 0))

theorem chooseFraming_grammar_iff (length : Option Nat) (chunked : Bool) (result : Framing) :
    chooseFraming length chunked = .ok result ↔ FramingGrammar length chunked result := by
  cases length <;> cases chunked <;> simp [chooseFraming, FramingGrammar, eq_comm]

/-- The exact bounded head delimiter; bodies and pipelined requests are outside
this interval. The scanner separately proves that this is the first delimiter. -/
def HeadBoundary (bytes : ByteArray) (stop : Nat) : Prop :=
  stop ≤ bytes.size ∧ 16 ≤ stop ∧ bytes[stop - 4]! = 13 ∧ bytes[stop - 3]! = 10 ∧
    bytes[stop - 2]! = 13 ∧ bytes[stop - 1]! = 10

/-- Complete supported origin-server head grammar. All syntax and field meaning
are independent productions proved above. The exact result includes routing
spans, connection policy, HEAD suppression, framing and Expect semantics.
CONNECT and unknown schemes/codings are grammatical but deliberately unsupported.
The byte comparator used for method selection has exact TextGrammar semantics. -/
def HeadGrammar (cfg : Config) (bytes : ByteArray) (stop : Nat) (head : Head) : Prop :=
  HeadBoundary bytes stop ∧
  let methodStart := if equals bytes 0 2 "\r\n" then 2 else 0
  ∃ line : RequestLine,
    (line.methodStart = methodStart ∧ RequestLineGrammar bytes stop line ∧
      line.targetEnd - line.targetStart ≤ cfg.maxTargetBytes) ∧
    ∃ target : TargetInfo,
      TargetGrammar bytes line.targetStart line.targetEnd
        (equals bytes methodStart line.methodEnd "OPTIONS")
        (equals bytes methodStart line.methodEnd "CONNECT") target ∧
      ∃ fields : HeaderState,
        HeadersMeaning cfg bytes stop line.minor line.headersStart
          { line := line.headersStart, colon := line.headersStart } fields ∧
        (fields.transferSeen = false ∨ fields.chunked = true) ∧
        ∃ framing : Framing, FramingGrammar fields.length fields.chunked framing ∧
          fields.unsupportedTransfer = false ∧ target.unsupportedScheme = false ∧
          equals bytes methodStart line.methodEnd "CONNECT" = false ∧
          head = ⟨{
            raw := bytes, methodStart, methodEnd := line.methodEnd
            targetStart := line.targetStart, targetEnd := line.targetEnd
            headersStart := line.headersStart, headEnd := stop
            close := fields.close || line.minor == 0
            isHead := equals bytes methodStart line.methodEnd "HEAD"
            versionMinor := line.minor
            pathStart := if target.authority.isSome then some target.pathStart else none
            authoritySpan := target.authority, schemeEnd := target.schemeEnd
          }, framing, fields.expectContinue⟩

/-- Every successful production request head, and every supported grammatical
head, agree on all returned fields. No native or application assumption is used. -/
theorem parseHead_grammar_iff (cfg : Config) (bytes : ByteArray) (stop : Nat) (head : Head) :
    parseHead cfg bytes stop = .ok head ↔ HeadGrammar cfg bytes stop head := by
  unfold parseHead HeadGrammar
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
  by_cases bad : (stop > bytes.size || stop < 16 || bytes[stop - 4]! != 13 ||
      bytes[stop - 3]! != 10 || bytes[stop - 2]! != 13 || bytes[stop - 1]! != 10) = true
  · have invalid : ¬HeadBoundary bytes stop := by
      intro valid
      obtain ⟨size, length, cr1, lf1, cr2, lf2⟩ := valid
      simp [show ¬stop > bytes.size by omega, show ¬stop < 16 by omega, cr1, lf1, cr2, lf2] at bad
    simp [bad, invalid]
  · have boundary : HeadBoundary bytes stop := by simpa [HeadBoundary, and_assoc] using bad
    have fieldIff := fun start minor result =>
      (parseHeaders_grammar_iff cfg bytes start stop minor result (by have := boundary.2.1; omega)
        boundary.1 boundary.2.2.2.2.1 boundary.2.2.2.2.2).symm
    simp only [bad, ↓reduceIte, boundary, true_and]
    simp only [←parseRequestLine_iff, ←parseTarget_iff, fieldIff, ←chooseFraming_grammar_iff]
    repeat' first | split | dsimp only
    all_goals simp [*] <;> try exact eq_comm
    all_goals grind

end FastHTTP.Protocol
