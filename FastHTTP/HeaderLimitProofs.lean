import FastHTTP.HeaderProofs
import FastHTTP.NumericProofs

namespace FastHTTP.Protocol

def HeaderBudget (cfg : Config) (state : HeaderState) : Prop :=
  ∀ n, state.length = some n → n ≤ cfg.maxBodyBytes

/-- Semantic interpretation of every field preserves the configured body bound.
Only Content-Length can set a fixed length; its production decimal parser has
already been proved against the positional decimal specification. -/
theorem parseField_budget (cfg : Config) (bytes : ByteArray) (i stop minor : Nat)
    (state result : HeaderState) (hs : HeaderBudget cfg state)
    (h : parseField cfg bytes i stop minor state = .ok result) : HeaderBudget cfg result := by
  unfold parseField at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' first | split at h | dsimp only at h
  all_goals try contradiction
  all_goals try (have numeric := (decimal_iff _ _ _ _ _).mp (by assumption))
  all_goals cases h
  all_goals simp_all [HeaderBudget]

theorem parseHeaders_loop_budget (cfg : Config) (bytes : ByteArray) (stop minor i : Nat)
    (state result : HeaderState) (hs : HeaderBudget cfg state)
    (h : parseHeaders.loop cfg bytes stop minor i state = .ok result) : HeaderBudget cfg result := by
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
          have nextBudget := parseField_budget cfg bytes line.valueEnd stop minor
            { state with line := i, colon := line.colon } nextState hs he
          exact parseHeaders_loop_budget cfg bytes stop minor line.next nextState result nextBudget h
  next hi =>
    split at h
    next hn => contradiction
    next hp => cases h; exact hs
termination_by stop - 2 - i

theorem parseHeaders_budget (cfg : Config) (bytes : ByteArray) (start stop minor : Nat)
    (result : HeaderState) (h : parseHeaders cfg bytes start stop minor = .ok result) :
    HeaderBudget cfg result := by
  exact parseHeaders_loop_budget cfg bytes stop minor start _ result (by simp [HeaderBudget]) h

/-- Successful framing cannot introduce a length absent from the bounded fields. -/
theorem chooseFraming_budget (cfg : Config) (fields : HeaderState) (framing : Framing)
    (hs : HeaderBudget cfg fields) (h : chooseFraming fields.length fields.chunked = .ok framing) :
    ∀ n, framing = .fixed n → n ≤ cfg.maxBodyBytes := by
  unfold chooseFraming at h
  cases hl : fields.length <;> cases hc : fields.chunked <;> simp_all [HeaderBudget]
  all_goals subst framing; simp_all

/-- Every accepted request's fixed-body length fits the configured limit. -/
theorem parseHead_budget (cfg : Config) (bytes : ByteArray) (stop : Nat) (head : Head)
    (h : parseHead cfg bytes stop = .ok head) :
    (∀ n, head.framing = .fixed n → n ≤ cfg.maxBodyBytes) ∧ head.request.body = .empty := by
  unfold parseHead at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · contradiction
  · try dsimp only at h
    cases hl : parseRequestLine bytes (if equals bytes 0 2 "\r\n" then 2 else 0) stop cfg.maxTargetBytes with
    | error status => simp [hl] at h
    | ok line =>
      simp only [hl] at h
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
          have budget := parseHeaders_budget cfg bytes line.headersStart stop line.minor fields hh
          split at h
          · contradiction
          · cases hf : chooseFraming fields.length fields.chunked with
            | error status => simp [hf] at h
            | ok framing =>
              simp only [hf] at h
              have framingBudget := chooseFraming_budget cfg fields framing budget hf
              split at h
              · contradiction
              · by_cases hconnect : equals bytes (if equals bytes 0 2 "\r\n" then 2 else 0) line.methodEnd "CONNECT" = true
                · simp [hconnect] at h
                · simp only [hconnect] at h
                  cases h
                  exact ⟨framingBudget, rfl⟩

end FastHTTP.Protocol
