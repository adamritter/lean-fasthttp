import FastHTTP.Protocol
import FastHTTP.LexicalProofs

namespace FastHTTP.Protocol

/-- The header block is a sequence of grammatical field lines ending at the
empty CRLF. This grammar is independent of the semantic header dispatcher. -/
inductive HeaderGrammar (bytes : ByteArray) (stop : Nat) : Nat → Prop where
  | empty {start : Nat} : start + 2 = stop → bytes[start]! = 13 → bytes[start + 1]! = 10 →
      HeaderGrammar bytes stop start
  | field (line : FieldLine) : FieldLineGrammar bytes stop line →
      HeaderGrammar bytes stop line.next → HeaderGrammar bytes stop line.start

theorem parseHeaders_loop_sound (cfg : Config) (bytes : ByteArray) (stop minor i : Nat)
    (state result : HeaderState) (hstop : 2 ≤ stop)
    (hcr : bytes[stop - 2]! = 13) (hlf : bytes[stop - 1]! = 10)
    (h : parseHeaders.loop cfg bytes stop minor i state = .ok result) :
    HeaderGrammar bytes stop i := by
  rw [parseHeaders.loop] at h
  split at h
  next hi =>
    cases hf : parseFieldLine bytes i stop with
    | none => simp [hf] at h
    | some line =>
      simp only [hf] at h
      split at h
      next hn => contradiction
      next hp =>
        split at h
        next err he => contradiction
        next nextState he =>
          have grammar := parseFieldLine_sound bytes i stop line hf
          have tail := parseHeaders_loop_sound cfg bytes stop minor line.next nextState result hstop hcr hlf h
          have result := HeaderGrammar.field line grammar.2 tail
          simpa [grammar.1] using result
  next hi =>
    split at h
    next hn => contradiction
    next hp =>
      have hb : i = stop - 2 := by
        simp only [Bool.or_eq_true, not_or] at hp
        simpa using hp.1
      subst i
      exact .empty (by omega) hcr (by simpa [show stop - 2 + 1 = stop - 1 by omega] using hlf)
termination_by stop - 2 - i

theorem parseHeaders_sound (cfg : Config) (bytes : ByteArray) (start stop minor : Nat)
    (result : HeaderState) (hstop : 2 ≤ stop)
    (hcr : bytes[stop - 2]! = 13) (hlf : bytes[stop - 1]! = 10)
    (h : parseHeaders cfg bytes start stop minor = .ok result) :
    HeaderGrammar bytes stop start :=
  parseHeaders_loop_sound cfg bytes stop minor start _ result hstop hcr hlf h

def requestLineOf (r : Request) : RequestLine :=
  ⟨r.methodStart, r.methodEnd, r.targetStart, r.targetEnd, r.headersStart, r.versionMinor⟩

/-- The accepted request head has a grammatical request-line and field block,
with the exact original octets and offsets returned to the application. This
structural theorem does not assume the result of either lexical parser. -/
theorem parseHead_envelope (cfg : Config) (bytes : ByteArray) (stop : Nat) (head : Head)
    (h : parseHead cfg bytes stop = .ok head) :
    head.request.raw = bytes ∧ head.request.headEnd = stop ∧
    RequestLineGrammar bytes stop (requestLineOf head.request) ∧
    HeaderGrammar bytes stop head.request.headersStart ∧
    head.request.targetEnd - head.request.targetStart ≤ cfg.maxTargetBytes := by
  unfold parseHead at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · contradiction
  · rename_i hb
    have bounds : stop ≤ bytes.size ∧ 16 ≤ stop ∧ bytes[stop - 4]! = 13 ∧
        bytes[stop - 3]! = 10 ∧ bytes[stop - 2]! = 13 ∧ bytes[stop - 1]! = 10 := by
      simpa [and_assoc] using hb
    have hcr := bounds.2.2.2.2.1
    have hlf := bounds.2.2.2.2.2
    try dsimp only at h
    cases hl : parseRequestLine bytes (if equals bytes 0 2 "\r\n" then 2 else 0) stop cfg.maxTargetBytes with
    | error status => simp [hl] at h
    | ok line =>
      simp only [hl] at h
      have lineGrammar := parseRequestLine_sound bytes _ stop cfg.maxTargetBytes line hl
      cases ht : parseTarget bytes line.targetStart line.targetEnd
          (equals bytes (if equals bytes 0 2 "\r\n" then 2 else 0) line.methodEnd "OPTIONS")
          (equals bytes (if equals bytes 0 2 "\r\n" then 2 else 0) line.methodEnd "CONNECT") with
      | error status => simp [ht] at h
      | ok target =>
        simp only [ht] at h
        cases hh : parseHeaders cfg bytes line.headersStart stop line.minor with
        | error status => simp [hh] at h
        | ok fields =>
          simp only [hh] at h
          have fieldsGrammar := parseHeaders_sound cfg bytes line.headersStart stop line.minor fields (by omega) hcr hlf hh
          split at h
          · contradiction
          · cases hf : chooseFraming fields.length fields.chunked with
            | error status => simp [hf] at h
            | ok framing =>
              simp only [hf] at h
              split at h
              · contradiction
              · by_cases hconnect : equals bytes (if equals bytes 0 2 "\r\n" then 2 else 0) line.methodEnd "CONNECT" = true
                · simp [hconnect] at h
                · simp only [hconnect] at h
                  cases h
                  refine ⟨rfl, rfl, ?_, fieldsGrammar, lineGrammar.2.2⟩
                  change RequestLineGrammar bytes stop
                    ⟨if equals bytes 0 2 "\r\n" then 2 else 0, line.methodEnd, line.targetStart,
                      line.targetEnd, line.headersStart, line.minor⟩
                  rw [← lineGrammar.1]
                  exact lineGrammar.2.1

end FastHTTP.Protocol
