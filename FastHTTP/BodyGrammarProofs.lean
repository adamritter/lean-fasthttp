import FastHTTP.BodyFastProofs
import FastHTTP.ChunkGrammarProofs
import FastHTTP.TrailerProofs

namespace FastHTTP.Protocol

/-- The complete bounded chunk-size line: a hexadecimal numeral followed by
zero or more RFC chunk extensions. Split points are grammatical witnesses. -/
def ChunkLineGrammar (line : ByteArray) (limit value : Nat) : Prop :=
  ∃ stop, 0 < stop ∧ stop ≤ line.size ∧
    HexadecimalEncoding (line.extract 0 stop).data.toList value ∧ value ≤ limit ∧
    ChunkExtensionsGrammar line stop

theorem hex_is_token (b : UInt8) (h : HexOctet b) : TokenOctet b := by
  simp [HexOctet, TokenOctet] at * <;> omega

theorem chunkSize_complete (line : ByteArray) (limit value : Nat)
    (h : ChunkLineGrammar line limit value) : chunkSize line limit = .ok value := by
  obtain ⟨stop, hs, hb, numeral, bound, extensions⟩ := h
  have chars : Octets line (fun b => hexDigit b = true) 0 stop := by
    intro i _ hi
    have len : i < (line.extract 0 stop).data.toList.length := by simp; omega
    have member : (line.extract 0 stop).data.toList[i] ∈ (line.extract 0 stop).data.toList :=
      List.mem_iff_getElem.mpr ⟨i, len, rfl⟩
    have digit := numeral.2.1 _ member
    have byte : (line.extract 0 stop).data.toList[i] = line[i]! := by
      simp only [Array.getElem_toList, ← ByteArray.getElem_eq_getElem_data,
        ByteArray.getElem_extract, Nat.zero_add]
      simp [getElem!_pos, show i < line.size by omega]
    rw [byte] at digit
    exact (hexDigit_iff _).mpr digit
  have lead := chunkExtensions_lead line stop extensions
  have last : stop = line.size ∨ hexDigit line[stop]! = false := by
    rcases lead.2.2 with h | h
    · exact Or.inl h
    · right
      cases hh : hexDigit line[stop]! with
      | false => rfl
      | true =>
        have ht := (token_iff _).mpr (hex_is_token _ ((hexDigit_iff _).mp hh))
        simp [h] at ht
  have scan := spanEnd_complete line line.size hexDigit 0 stop (by omega) hb chars last
  have number := (hexadecimal_iff line 0 stop limit value).mpr ⟨hs, hb, numeral, bound⟩
  have suffix := chunkExtensions_complete line stop extensions
  simp [chunkSize, scan, show stop ≠ 0 by omega, number, suffix]

theorem chunkSize_iff (line : ByteArray) (limit value : Nat) :
    chunkSize line limit = .ok value ↔ ChunkLineGrammar line limit value :=
  ⟨chunkSize_grammar line limit value, chunkSize_complete line limit value⟩

/-- Successful results only; rejected prefixes are not productions of the
accepted-message grammar. Resource-limit violations likewise have no production. -/
def BodySuccessful : BodyAction → Prop
  | .more _ | .done _ _ => True
  | .error _ => False

/-- RFC line accumulation for size/extension and trailer lines. CRLF is literal;
a lone LF or a CR followed by another byte has no successful production. -/
def BodyLineStep (cfg : Config) (s : BodyState) (trailing : Bool) (b : UInt8) (out : BodyAction) : Prop :=
  let next := if trailing then { s with trailerBytes := s.trailerBytes + 1 } else s
  (trailing = false ∨ next.trailerBytes ≤ cfg.maxTrailerBytes) ∧
  if s.sawCR then
    b = 10 ∧
    if trailing then
      ((s.line.isEmpty = true ∧ out = .done s.body s.trailers) ∨
        (s.line.isEmpty = false ∧ ∃ field, TrailerGrammar s.line field ∧
          out = .more { next with line := .empty, sawCR := false, trailers := s.trailers.push field }))
    else ∃ size, ChunkLineGrammar s.line (cfg.maxBodyBytes - s.body.size) size ∧
      (size = 0 ∨ s.chunks < cfg.maxChunks) ∧
      out = .more { next with
        phase := if size == 0 then .trailers else .data size
        line := .empty, sawCR := false, chunks := s.chunks + (if size == 0 then 0 else 1) }
  else
    (b = 13 ∧ out = .more { next with sawCR := true }) ∨
    (b ≠ 13 ∧ b ≠ 10 ∧ s.line.size < cfg.maxChunkLineBytes ∧ out = .more { next with line := s.line.push b })

/-- Independent operational grammar for the whole body, rather than only its
lexical helpers. Fixed and chunk data consume exactly one unchanged payload byte;
size lines, extension metadata, CRLF and trailers never become payload. The
initial zero-length fixed-body epsilon production is handled by BodyWire below. -/
def BodyByteGrammar (cfg : Config) (s : BodyState) (b : UInt8) (out : BodyAction) : Prop :=
  match s.phase with
  | .fixed remaining =>
    (remaining = 0 ∧ out = .done s.body s.trailers) ∨
    (remaining = 1 ∧ out = .done (s.body.push b) s.trailers) ∨
    (1 < remaining ∧ out = .more { s with body := s.body.push b, phase := .fixed (remaining - 1) })
  | .data remaining =>
    (remaining = 0 ∧ b = 13 ∧ out = .more { s with phase := .dataLF }) ∨
    (0 < remaining ∧ out = .more { s with body := s.body.push b, phase := if remaining == 1 then .dataCR else .data (remaining - 1) })
  | .dataCR => b = 13 ∧ out = .more { s with phase := .dataLF }
  | .dataLF => b = 10 ∧ out = .more { s with phase := .sizeLine }
  | .sizeLine => BodyLineStep cfg s false b out
  | .trailers => BodyLineStep cfg s true b out

theorem pair_witness {α β : Type} (pair : α × β) (property : α → β → Prop) :
    (∃ a b, pair = (a, b) ∧ property a b) ↔ property pair.1 pair.2 := by
  constructor
  · rintro ⟨a, b, same, valid⟩
    simpa only [same] using valid
  · intro valid
    exact ⟨pair.1, pair.2, rfl, valid⟩

/-- Every successful byte transition is exactly a production of the independent
RFC body grammar; conversely every such production executes successfully. -/
theorem bodyByte_grammar (cfg : Config) (s : BodyState) (b : UInt8) (out : BodyAction)
    (success : BodySuccessful out) :
    bodyByte cfg s b = out ↔ BodyByteGrammar cfg s b out := by
  cases out with
  | error status => contradiction
  | more state | done body trailers =>
    cases hp : s.phase <;>
      simp [bodyByte, hp, BodyByteGrammar, BodyLineStep, ← chunkSize_iff, ← trailer_iff]
    all_goals repeat' split
    all_goals simp_all <;> try exact eq_comm
    all_goals try simp only [pair_witness, eq_comm]
    all_goals try rfl
    all_goals try omega
    all_goals constructor <;> intro h
    all_goals first | exact h.2 | exact ⟨by omega, h⟩

/-- Complete successful body wire grammar, including the zero-length epsilon
production. A terminal production ends the message; no subsequent pipeline byte
belongs to this derivation. Payload and raw trailer values are part of its index.
All transitions above use independent numeral, extension and trailer grammars. -/
inductive BodyWire (cfg : Config) : BodyState → List UInt8 → ByteArray → Array (String × ByteArray) → Prop where
  | empty {state : BodyState} : state.phase = .fixed 0 → BodyWire cfg state [] state.body state.trailers
  | finish {state : BodyState} {b : UInt8} {body : ByteArray} {trailers : Array (String × ByteArray)} :
      BodyLive state → BodyByteGrammar cfg state b (.done body trailers) → BodyWire cfg state [b] body trailers
  | next {state next : BodyState} {b : UInt8} {wire : List UInt8} {body : ByteArray}
      {trailers : Array (String × ByteArray)} :
      BodyLive state → BodyByteGrammar cfg state b (.more next) → BodyWire cfg next wire body trailers →
      BodyWire cfg state (b :: wire) body trailers

/-- Every grammatical body is executed exactly, including all accumulated bytes,
trailers and its consumed length. No production parser hypothesis is required. -/
theorem bodyWire_fold (cfg : Config) (state : BodyState) (wire : List UInt8) (body : ByteArray)
    (trailers : Array (String × ByteArray)) (grammar : BodyWire cfg state wire body trailers) (count : Nat) :
    wire.foldl (bodyAdvance cfg) (bodyInitial state count) = ⟨.done body trailers, count + wire.length⟩ := by
  induction grammar generalizing count with
  | empty zero => simp [bodyInitial, zero]
  | @finish state b body trailers live byte =>
    have step := (bodyByte_grammar cfg state b (.done body trailers) (by trivial)).mpr byte
    simp [bodyInitial_live state count live, bodyAdvance, step]
  | @next state next b wire body trailers live byte rest ih =>
    have step := (bodyByte_grammar cfg state b (.more next) (by trivial)).mpr byte
    have nextLive := bodyByte_live cfg state next b step
    have tail := ih (count + 1)
    rw [bodyInitial_live next (count + 1) nextLive] at tail
    simpa [bodyInitial_live state count live, List.foldl_cons, bodyAdvance, step,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using tail

/-- Every successful live execution consumes a grammatical prefix; the entire
remaining input is an untouched suffix, not part of the body grammar. -/
theorem bodyList_live_wire (cfg : Config) (wire : List UInt8) (state : BodyState) (count stop : Nat)
    (body : ByteArray) (trailers : Array (String × ByteArray)) (live : BodyLive state)
    (h : wire.foldl (bodyAdvance cfg) ⟨.more state, count⟩ = ⟨.done body trailers, stop⟩) :
    ∃ consumed suffix, wire = consumed ++ suffix ∧ BodyWire cfg state consumed body trailers ∧
      stop = count + consumed.length := by
  induction wire generalizing state count with
  | nil => cases h
  | cons b rest ih =>
    simp only [List.foldl_cons, bodyAdvance] at h
    cases step : bodyByte cfg state b with
    | error status =>
      rw [step, bodyList_terminal cfg ⟨.error status, count + 1⟩ rest (by trivial)] at h
      cases h
    | done payload raw =>
      rw [step, bodyList_terminal cfg ⟨.done payload raw, count + 1⟩ rest (by trivial)] at h
      cases h
      exact ⟨[b], rest, rfl, .finish live ((bodyByte_grammar cfg state b (.done _ _) (by trivial)).mp step), rfl⟩
    | more next =>
      rw [step] at h
      obtain ⟨consumed, suffix, bytes, grammar, stopped⟩ := ih next (count + 1)
        (bodyByte_live cfg state next b step) h
      refine ⟨b :: consumed, suffix, by simp [bytes],
        .next live ((bodyByte_grammar cfg state b (.more next) (by trivial)).mp step) grammar, ?_⟩
      simp only [List.length_cons]
      omega

theorem bodyList_wire (cfg : Config) (wire : List UInt8) (state : BodyState) (count stop : Nat)
    (body : ByteArray) (trailers : Array (String × ByteArray))
    (h : wire.foldl (bodyAdvance cfg) (bodyInitial state count) = ⟨.done body trailers, stop⟩) :
    ∃ consumed suffix, wire = consumed ++ suffix ∧ BodyWire cfg state consumed body trailers ∧
      stop = count + consumed.length := by
  by_cases live : BodyLive state
  · rw [bodyInitial_live state count live] at h
    exact bodyList_live_wire cfg wire state count stop body trailers live h
  · have zero : state.phase = .fixed 0 := by
      cases hp : state.phase <;> simp_all [BodyLive]
    have initial : bodyInitial state count = ⟨.done state.body state.trailers, count⟩ := by
      simp [bodyInitial, zero]
    rw [initial, bodyList_terminal cfg ⟨.done state.body state.trailers, count⟩ wire (by trivial)] at h
    cases h
    exact ⟨[], wire, rfl, .empty zero, by simp⟩

theorem bodyScan_done_iff (scan : BodyScan) (body : ByteArray) (trailers : Array (String × ByteArray)) (stop : Nat) :
    scan.result = .done body trailers stop ↔ scan = ⟨.done body trailers, stop⟩ := by
  cases scan with
  | mk action count => cases action <;> simp [BodyScan.result, and_assoc]

/-- Whole-message correctness of the actual optimized body decoder. Acceptance
is equivalent to an independent complete body derivation followed by an arbitrary
pipeline suffix. The theorem includes the exact binary body, raw trailers and
first stop offset, and covers every Config, initial state and input buffer. -/
theorem decodeBody_grammar_iff (cfg : Config) (bytes : ByteArray) (start : Nat) (state : BodyState)
    (body : ByteArray) (trailers : Array (String × ByteArray)) (stop : Nat) :
    decodeBody cfg bytes start state = .done body trailers stop ↔
      ∃ consumed suffix, bytes.data.toList.drop start = consumed ++ suffix ∧
        BodyWire cfg state consumed body trailers ∧ stop = start + consumed.length := by
  rw [decodeBody_eq_reference, decodeBodyReference, bodyScan_done_iff, bodyLoop_eq_fold]
  constructor
  · exact bodyList_wire cfg _ state start stop body trailers
  · rintro ⟨consumed, suffix, input, grammar, last⟩
    rw [input, List.foldl_append, bodyWire_fold cfg state consumed body trailers grammar start,
      bodyList_terminal cfg ⟨.done body trailers, start + consumed.length⟩ suffix (by trivial)]
    simp [last]

/-- The RFC chunked-body instance starts with an empty size line and payload.
This is the initial state constructed by the production HTTP header dispatcher. -/
theorem decodeChunked_grammar_iff (cfg : Config) (bytes : ByteArray) (body : ByteArray)
    (trailers : Array (String × ByteArray)) (stop : Nat) :
    decodeBody cfg bytes 0 { phase := .sizeLine } = .done body trailers stop ↔
      ∃ consumed suffix, bytes.data.toList = consumed ++ suffix ∧
        BodyWire cfg { phase := .sizeLine } consumed body trailers ∧ stop = consumed.length := by
  simpa using decodeBody_grammar_iff cfg bytes 0 { phase := .sizeLine } body trailers stop

end FastHTTP.Protocol
