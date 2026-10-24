import FastHTTP.HeadGrammarProofs
import FastHTTP.ScannerProofs
import FastHTTP.FeedProofs

namespace FastHTTP.Protocol

/-- Exact successful body interpretation including the metadata update and the
untouched pipeline suffix. The wire prefix uses the independent BodyWire grammar. -/
def BodyCompletionGrammar (cfg : Config) (bytes : ByteArray) (start : Nat) (decoder : BodyState)
    (initial result : Request) (rest : ByteArray) : Prop :=
  ∃ body trailers stop,
    (∃ consumed suffix, bytes.data.toList.drop start = consumed ++ suffix ∧
      BodyWire cfg decoder consumed body trailers ∧ stop = start + consumed.length) ∧
    result = { initial with body, rawTrailers := trailers } ∧ rest = bytes.extract stop bytes.size

theorem bodyStep_grammar_iff (cfg : Config) (bytes : ByteArray) (start : Nat) (decoder : BodyState)
    (initial result : Request) (rest : ByteArray) :
    bodyStep cfg initial decoder bytes start = .request result rest ↔
      BodyCompletionGrammar cfg bytes start decoder initial result rest := by
  unfold BodyCompletionGrammar
  simp only [←decodeBody_grammar_iff]
  cases parsed : decodeBody cfg bytes start decoder <;> simp [bodyStep, parsed, and_assoc, eq_comm]

/-- Acknowledgment is a logical observation point: the real driver sends the
100 response before executing this continuation. It never fabricates body bytes. -/
def acknowledge (cfg : Config) : Step → Step
  | .«continue» state => feed cfg state .empty
  | other => other

theorem acknowledge_bodyStep (cfg : Config) (request : Request) (decoder : BodyState)
    (bytes : ByteArray) (start : Nat) :
    acknowledge cfg (bodyStep cfg request decoder bytes start) = bodyStep cfg request decoder bytes start := by
  unfold bodyStep
  cases decodeBody cfg bytes start decoder <;> rfl

theorem acknowledge_continue_body (cfg : Config) (request : Request) (decoder : BodyState)
    (pending : ByteArray) (start : Nat) :
    acknowledge cfg (.«continue» (.body request decoder pending start)) =
      bodyStep cfg request decoder pending start := by
  simp only [acknowledge, feed]
  rw [append_unless_empty]
  simp

def HeadBodyGrammar (cfg : Config) (bytes : ByteArray) (stop : Nat) (head : Head)
    (request : Request) (rest : ByteArray) : Prop :=
  if head.framing == .fixed 0 then request = head.request ∧ rest = bytes.extract stop bytes.size
  else BodyCompletionGrammar cfg bytes stop
    { phase := match head.framing with | .fixed n => .fixed n | .chunked => .sizeLine }
    head.request request rest

/-- Complete first-message grammar with a bounded, first-delimiter search. Its
head and body productions are independent of the production parser; following
pipeline octets remain in rest. The Expect flag does not change message content. -/
def RequestWire (cfg : Config) (bytes : ByteArray) (request : Request) (rest : ByteArray) : Prop :=
  let scan := referenceScan cfg.maxHeaderBytes [] bytes.data.toList
  scan.invalid = false ∧ ∃ stop, scan.stop = some stop ∧ ∃ head,
    HeadGrammar cfg (bytes.extract 0 stop) stop head ∧ HeadBodyGrammar cfg bytes stop head request rest

theorem headStep_grammar_iff (cfg : Config) (bytes : ByteArray) (scanner : ScanState)
    (request : Request) (rest : ByteArray) :
    acknowledge cfg (headStep cfg bytes scanner) = .request request rest ↔
      scanner.invalid = false ∧ ∃ stop, scanner.stop = some stop ∧ ∃ head,
        HeadGrammar cfg (bytes.extract 0 stop) stop head ∧ HeadBodyGrammar cfg bytes stop head request rest := by
  simp only [←parseHead_grammar_iff]
  cases invalid : scanner.invalid
  · cases stopped : scanner.stop with
    | none => simp [headStep, invalid, stopped, acknowledge]
    | some stop =>
      cases parsed : parseHead cfg (bytes.extract 0 stop) stop with
      | error status => simp [headStep, invalid, stopped, parsed, acknowledge]
      | ok head =>
        by_cases zero : (head.framing == .fixed 0) = true
        · simp [headStep, invalid, stopped, parsed, HeadBodyGrammar, zero, acknowledge]
          constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1.symm, h2.symm⟩
        · cases expected : head.expectContinue <;>
            simp [headStep, invalid, stopped, parsed, HeadBodyGrammar, zero, expected,
              acknowledge_continue_body, acknowledge_bodyStep, bodyStep_grammar_iff] <;> rfl
  · simp [headStep, invalid, acknowledge]

/-- End-to-end pure request parsing: arbitrary bytes produce a complete Request
(after the required Expect acknowledgment) iff they contain a grammatical first
message with exactly that metadata, binary body, trailers and pipeline remainder. -/
theorem feed_request_grammar_iff (cfg : Config) (bytes : ByteArray) (request : Request) (rest : ByteArray) :
    acknowledge cfg (feed cfg .head bytes) = .request request rest ↔ RequestWire cfg bytes request rest := by
  simp only [feed, append_unless_empty, ByteArray.empty_append, scanFeedFast_reference]
  exact headStep_grammar_iff cfg bytes _ request rest

/-- Arbitrarily fragmented input has the same complete request grammar, including
fragments buffered while Expect awaits acknowledgment. No projection discards
request fields or the pipeline suffix from this statement. -/
theorem feed_fragmented_grammar_iff (cfg : Config) (chunks : List ByteArray)
    (request : Request) (rest : ByteArray) :
    acknowledge cfg (chunks.foldl (appendStep cfg) (feed cfg .head .empty)) = .request request rest ↔
      RequestWire cfg (chunks.foldl (· ++ ·) .empty) request rest := by
  rw [feed_fragments cfg .head chunks .empty initial_state_bound]
  exact feed_request_grammar_iff cfg _ request rest

/-- A production Expect continuation always retains an already-validated head
and a body decoder; acknowledgment cannot restart header parsing. -/
theorem headStep_no_head_continue (cfg : Config) (bytes pending : ByteArray)
    (scanner next : ScanState) : headStep cfg bytes scanner ≠ .«continue» (.head pending next) := by
  unfold headStep
  repeat' first | split | dsimp only
  all_goals try simp
  all_goals unfold bodyStep
  all_goals split <;> simp

def ContinuationBound : Step → Prop
  | .«continue» (.head _ _) => False
  | .«continue» (.body _ _ pending start) => start ≤ pending.size
  | _ => True

theorem feed_continuation_bound (cfg : Config) (state : State) (bytes : ByteArray) (hs : StateBound state) :
    ContinuationBound (feed cfg state bytes) := by
  have bound := feed_bound cfg state bytes hs
  cases output : feed cfg state bytes with
  | need next => trivial
  | request request rest => trivial
  | reject status => trivial
  | «continue» next =>
    cases next with
    | body request decoder pending start => simpa [output, StepBound, StateBound, ContinuationBound] using bound
    | head pending scanner =>
      cases state with
      | body request decoder buffered start => exact False.elim (feed_body_no_continue cfg request decoder buffered bytes start _ output)
      | head buffered scan => exact False.elim (headStep_no_head_continue cfg _ pending _ scanner output)

theorem acknowledge_append (cfg : Config) (step : Step) (bytes : ByteArray) (hs : ContinuationBound step) :
    acknowledge cfg (appendStep cfg step bytes) =
      acknowledge cfg (appendStep cfg (acknowledge cfg step) bytes) := by
  cases step with
  | need state => rfl
  | request request rest => rfl
  | reject status => rfl
  | «continue» state =>
    cases state with
    | head pending scanner => contradiction
    | body request decoder pending start =>
      simp only [appendStep, acknowledge_continue_body]
      change bodyStep cfg request decoder (pending ++ bytes) start =
        acknowledge cfg (appendStep cfg (bodyStep cfg request decoder pending start) bytes)
      rw [←bodyStep_append_start cfg request decoder pending bytes start hs]
      exact (acknowledge_bodyStep cfg request decoder (pending ++ bytes) start).symm

/-- The time at which the driver sends and acknowledges 100-continue cannot
change parsing: acknowledging between receive fragments equals acknowledging
after the concatenated input. The equality keeps the complete result. -/
theorem feed_acknowledged_fragmentation (cfg : Config) (a b : ByteArray) :
    acknowledge cfg (feed cfg .head (a ++ b)) =
      acknowledge cfg (appendStep cfg (acknowledge cfg (feed cfg .head a)) b) := by
  rw [feed_initial_fragmentation]
  exact acknowledge_append cfg (feed cfg .head a) b (feed_continuation_bound cfg .head a initial_state_bound)

/-- Whole-request grammar for a real receiver that acknowledges Expect as soon
as each fragment is processed, rather than buffering all fragments first. -/
theorem feed_acknowledged_fragments (cfg : Config) (chunks : List ByteArray) (prior : ByteArray) :
    chunks.foldl (fun step bytes => acknowledge cfg (appendStep cfg step bytes))
      (acknowledge cfg (feed cfg .head prior)) =
        acknowledge cfg (feed cfg .head (chunks.foldl (· ++ ·) prior)) := by
  induction chunks generalizing prior with
  | nil => rfl
  | cons bytes rest ih =>
    simp only [List.foldl_cons]
    rw [←feed_acknowledged_fragmentation]
    exact ih (prior ++ bytes)

theorem feed_live_fragments_grammar_iff (cfg : Config) (chunks : List ByteArray)
    (request : Request) (rest : ByteArray) :
    chunks.foldl (fun step bytes => acknowledge cfg (appendStep cfg step bytes))
      (acknowledge cfg (feed cfg .head .empty)) = .request request rest ↔
        RequestWire cfg (chunks.foldl (· ++ ·) .empty) request rest := by
  rw [feed_acknowledged_fragments]
  exact feed_request_grammar_iff cfg _ request rest

end FastHTTP.Protocol
