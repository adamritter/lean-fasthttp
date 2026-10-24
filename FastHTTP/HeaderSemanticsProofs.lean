import FastHTTP.FieldsProofs
import FastHTTP.HeaderProofs
import FastHTTP.NumericProofs
import FastHTTP.TrailerProofs
import FastHTTP.BodyGrammarProofs

namespace FastHTTP.Protocol

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-- Unique OWS trimming; an all-OWS value uses the empty interval at its end.
This convention specifies an offset, not any additional accepted field syntax. -/
def CanonicalTrimmed (bytes : ByteArray) (start stop first last : Nat) : Prop :=
  Trimmed bytes start stop first last ∧ (first = last → first = stop)

theorem canonicalTrimmed_sound (bytes : ByteArray) (start stop : Nat) (hs : start ≤ stop) :
    CanonicalTrimmed bytes start stop (spanEnd bytes stop space start)
      (trimEnd bytes (spanEnd bytes stop space start) stop) := by
  have trimmed := trimSpan_spec bytes start stop hs
  have scan := spanEnd_spec bytes stop space start hs
  refine ⟨trimmed, ?_⟩
  intro empty
  rcases scan.2.2.2 with done | edge
  · exact done
  · by_cases ended : spanEnd bytes stop space start = stop
    · exact ended
    · have ws := trimmed.2.2.2.2.1 (spanEnd bytes stop space start) (by omega) (by omega)
      have ha := (space_iff _).mpr ws
      simp [edge] at ha

theorem canonicalTrimmed_complete (bytes : ByteArray) (start stop first last : Nat)
    (h : CanonicalTrimmed bytes start stop first last) :
    spanEnd bytes stop space start = first ∧ trimEnd bytes first stop = last := by
  obtain ⟨⟨hs, hf, hl, leading, trailing, edge⟩, canonical⟩ := h
  rcases edge with empty | ⟨hfirst, hlast⟩
  · have ended := canonical empty
    subst last
    subst first
    have scan := spanEnd_complete bytes stop space start stop hs (by omega)
      (fun i hi hj => (space_iff _).mpr (leading i hi hj)) (Or.inl rfl)
    simp [scan, trimEnd]
  · exact ⟨spanEnd_complete bytes stop space start first hs (by omega)
        (fun i hi hj => (space_iff _).mpr (leading i hi hj)) (Or.inr hfirst),
      trimEnd_complete bytes first stop last hf hl trailing (Or.inr hlast)⟩

theorem extract_octets (bytes : ByteArray) (start stop : Nat) (p : UInt8 → Prop)
    (hb : stop ≤ bytes.size) (h : ∀ b ∈ (bytes.extract start stop).data.toList, p b) :
    Octets bytes p start stop := by
  intro i hi hj
  have len : i - start < (bytes.extract start stop).data.toList.length := by simp; omega
  have member : (bytes.extract start stop).data.toList[i - start] ∈ (bytes.extract start stop).data.toList :=
    List.mem_iff_getElem.mpr ⟨i - start, len, rfl⟩
  have value := h _ member
  have byte : (bytes.extract start stop).data.toList[i - start] = bytes[i]! := by
    simp only [Array.getElem_toList, ← ByteArray.getElem_eq_getElem_data, ByteArray.getElem_extract]
    simp [Nat.add_sub_of_le hi, getElem!_pos, show i < bytes.size by omega]
  simpa only [byte] using value

/-- The independent decimal grammar implies the production's preliminary digit
scan. This discharges that check rather than assuming its outcome in the spec. -/
theorem decimal_success_span (bytes : ByteArray) (first last limit value : Nat)
    (h : decimal bytes first last limit = some value) :
    first < last ∧ last ≤ bytes.size ∧ spanEnd bytes last (fun b => b >= 48 && b <= 57) first = last := by
  have number := (decimal_iff bytes first last limit value).mp h
  have chars := extract_octets bytes first last DecimalOctet number.2.1 number.2.2.1.2.1
  exact ⟨number.1, number.2.1,
    spanEnd_complete bytes last _ first last (by omega) (by omega)
      (fun i hi hj => (decimalOctet_iff _).mpr (chars i hi hj)) (Or.inl rfl)⟩

/-- Independent semantic interpretation of one validated field envelope. The
name classifier has exact byte-text semantics by equals_iff. Values use their
independent RFC grammars; the returned record includes all accumulated flags. -/
def HeaderValueGrammar (cfg : Config) (bytes : ByteArray) (first last next minor : Nat)
    (initial result : HeaderState) : Prop :=
  if equals bytes initial.line initial.colon "content-length" true then
    initial.length = none ∧ ∃ value,
      (first < last ∧ last ≤ bytes.size ∧ DecimalEncoding (bytes.extract first last).data.toList value ∧
        value ≤ cfg.maxBodyBytes) ∧
      result = { initial with length := some value, line := next, colon := next }
  else if equals bytes initial.line initial.colon "transfer-encoding" true then
    minor ≠ 0 ∧ ∃ chunked unsupported,
      (first ≤ last ∧ last ≤ bytes.size ∧ TransferListGrammar bytes last first initial.chunked false (chunked, unsupported)) ∧
      result = { initial with chunked, transferSeen := true, unsupportedTransfer := initial.unsupportedTransfer || unsupported, line := next, colon := next }
  else if equals bytes initial.line initial.colon "host" true then
    initial.host = false ∧ AuthorityGrammar bytes first last false ∧
      result = { initial with host := true, line := next, colon := next }
  else if minor != 0 && equals bytes initial.line initial.colon "expect" true then
    initial.expectContinue = false ∧ TextGrammar bytes first last "100-continue" true ∧
      result = { initial with expectContinue := true, line := next, colon := next }
  else if equals bytes initial.line initial.colon "connection" true then
    ∃ closing, (first ≤ last ∧ last ≤ bytes.size ∧ ConnectionListGrammar bytes last first false closing) ∧
      result = { initial with close := initial.close || closing, line := next, colon := next }
  else result = { initial with line := next, colon := next }

def HeaderFieldGrammar (cfg : Config) (bytes : ByteArray) (i minor : Nat)
    (initial result : HeaderState) : Prop :=
  ∃ first last, CanonicalTrimmed bytes (initial.colon + 1) i first last ∧
    HeaderValueGrammar cfg bytes first last (i + 2) minor initial result

theorem headerField_trim (cfg : Config) (bytes : ByteArray) (i minor : Nat)
    (initial result : HeaderState) (hs : initial.colon + 1 ≤ i) :
    HeaderFieldGrammar cfg bytes i minor initial result ↔
      HeaderValueGrammar cfg bytes (spanEnd bytes i space (initial.colon + 1))
        (trimEnd bytes (spanEnd bytes i space (initial.colon + 1)) i) (i + 2) minor initial result := by
  constructor
  · rintro ⟨first, last, trimmed, value⟩
    have eqs := canonicalTrimmed_complete bytes _ i first last trimmed
    simpa only [eqs.1, eqs.2] using value
  · intro value
    exact ⟨_, _, canonicalTrimmed_sound bytes _ i hs, value⟩

/-- Exact semantic field-state update for every grammatical field envelope.
Duplicate framing/Host fields and unsupported expectations have no successful
production; header order and repeated Transfer-Encoding lines are fully tracked. -/
theorem parseField_grammar_iff (cfg : Config) (bytes : ByteArray) (i stop minor : Nat)
    (initial result : HeaderState) (hn : initial.line < initial.colon)
    (hv : initial.colon + 1 ≤ i) (hi : i + 1 < stop) (hb : stop ≤ bytes.size)
    (lf : bytes[i + 1]! = 10) :
    parseField cfg bytes i stop minor initial = .ok result ↔ HeaderFieldGrammar cfg bytes i minor initial result := by
  rw [headerField_trim cfg bytes i minor initial result hv]
  have first := spanEnd_spec bytes i space (initial.colon + 1) hv
  have last := trimEnd_spec bytes (spanEnd bytes i space (initial.colon + 1)) i first.2.1
  unfold parseField HeaderValueGrammar
  simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
  simp only [show ¬ i + 1 ≥ stop by omega, decide_false, lf, bne_self_eq_false,
    show (initial.colon == initial.line) = false by simp [Nat.ne_of_gt hn], Bool.or_self,
    Bool.false_eq_true, ↓reduceIte]
  simp only [← decimal_iff, ← transferCodings_iff, ← validAuthority_iff, ← equals_iff,
    ← connectionOptions_iff]
  generalize hfirst : spanEnd bytes i space (initial.colon + 1) = firstIndex at *
  generalize hlast : trimEnd bytes firstIndex i = lastIndex at *
  repeat' first | split | dsimp only
  all_goals try (have numeric := decimal_success_span _ _ _ _ _ (by assumption))
  all_goals simp only [Bool.or_eq_true, Bool.not_eq_true, beq_iff_eq, bne_iff_ne,
    not_or, Decidable.not_not, Option.isSome_iff_ne_none] at *
  all_goals simp [*, pair_witness, and_assoc] <;> try omega
  all_goals try exact eq_comm
  all_goals try (intro value hdecimal; have digits := decimal_success_span _ _ _ _ _ hdecimal; omega)
  all_goals try grind
  rename_i transfer pending pair parsed notLength version
  rcases pair with ⟨a, b⟩
  cases a <;> cases b <;> simp [eq_comm]

end FastHTTP.Protocol
