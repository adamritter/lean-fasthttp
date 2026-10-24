import FastHTTP.Fields
import FastHTTP.TargetProofs
import FastHTTP.ChunkGrammarProofs

namespace FastHTTP.Protocol

def ListSpaceOctet (b : UInt8) : Prop := SpaceOctet b ∨ b.toNat = 44

theorem listSpace_iff (b : UInt8) : listSpace b = true ↔ ListSpaceOctet b := by
  unfold listSpace
  rw [Bool.or_eq_true, space_iff]
  simp [ListSpaceOctet, ← UInt8.toNat_inj]

/-- One Connection option, its following OWS, and its field/list delimiter.
The name comparison is already proved equivalent to exact ASCII-folded text. -/
def ConnectionTokenGrammar (bytes : ByteArray) (start stop : Nat) (closing : Bool) (last : Nat) : Prop :=
  ∃ nameEnd, TokenGrammar bytes start nameEnd ∧ Whitespace bytes nameEnd last ∧ last ≤ stop ∧
    (last = stop ∨ bytes[last]! = 44) ∧ closing = equals bytes start nameEnd "close" true

theorem connectionToken_sound (bytes : ByteArray) (start stop : Nat) (closing : Bool) (last : Nat)
    (hs : start ≤ stop) (hb : stop ≤ bytes.size)
    (h : connectionToken bytes start stop = .ok (closing, last)) :
    ConnectionTokenGrammar bytes start stop closing last := by
  have name := spanEnd_spec bytes stop token start hs
  have ws := spanEnd_spec bytes stop space _ name.2.1
  unfold connectionToken at h
  dsimp only at h
  split at h
  · contradiction
  · rename_i hg
    have guard : spanEnd bytes stop token start ≠ start ∧
        (spanEnd bytes stop space (spanEnd bytes stop token start) < stop →
          bytes[spanEnd bytes stop space (spanEnd bytes stop token start)]! = 44) := by
      simpa using hg
    cases h
    refine ⟨_, ⟨by omega, by omega, fun i hi hj => (token_iff _).mp (name.2.2.1 i hi hj)⟩,
      ⟨ws.1, by omega, fun i hi hj => (space_iff _).mp (ws.2.2.1 i hi hj)⟩,
      ws.2.1, ?_, rfl⟩
    by_cases he : spanEnd bytes stop space (spanEnd bytes stop token start) = stop
    · exact Or.inl he
    · exact Or.inr (guard.2 (by omega))

theorem connectionToken_complete (bytes : ByteArray) (start stop : Nat) (closing : Bool) (last : Nat)
    (h : ConnectionTokenGrammar bytes start stop closing last) :
    connectionToken bytes start stop = .ok (closing, last) := by
  obtain ⟨nameEnd, name, ws, he, delim, rfl⟩ := h
  dsimp only [TokenGrammar, Whitespace] at name ws
  have tokenStop : nameEnd = stop ∨ token bytes[nameEnd]! = false := by
    by_cases hn : nameEnd = last
    · rcases delim with hd | hd
      · exact Or.inl (by omega)
      · exact Or.inr (by simp [hn, hd, token])
    · exact Or.inr (space_not_token _ (ws.2.2 nameEnd (by omega) (by omega)))
  have nscan := spanEnd_complete bytes stop token start nameEnd (by omega) (by omega)
    (fun i hi hj => (token_iff _).mpr (name.2.2 i hi hj)) tokenStop
  have wscan := spanEnd_complete bytes stop space nameEnd last ws.1 he
    (fun i hi hj => (space_iff _).mpr (ws.2.2 i hi hj))
    (by rcases delim with hd | hd; exact Or.inl hd; exact Or.inr (by simp [hd, space]))
  have hn : nameEnd ≠ start := by omega
  have noBad : ¬(last < stop ∧ bytes[last]! ≠ 44) := by
    rcases delim with hd | hd
    · omega
    · simp [hd]
  simp [connectionToken, nscan, wscan, hn, noBad]

theorem connectionToken_iff (bytes : ByteArray) (start stop : Nat) (closing : Bool) (last : Nat)
    (hs : start ≤ stop) (hb : stop ≤ bytes.size) :
    connectionToken bytes start stop = .ok (closing, last) ↔
      ConnectionTokenGrammar bytes start stop closing last :=
  ⟨connectionToken_sound bytes start stop closing last hs hb,
    connectionToken_complete bytes start stop closing last⟩

/-- A complete RFC recipient comma-list. Empty members are ignored. The Boolean
is precisely the accumulated disjunction of case-insensitive 'close' options. -/
inductive ConnectionListGrammar (bytes : ByteArray) (stop : Nat) : Nat → Bool → Bool → Prop where
  | empty {start : Nat} (closing : Bool) :
      Delimited bytes start stop listSpace stop → ConnectionListGrammar bytes stop start closing closing
  | last {start first : Nat} (prior closing : Bool) :
      Delimited bytes start stop listSpace first → first < stop →
      ConnectionTokenGrammar bytes first stop closing stop →
      ConnectionListGrammar bytes stop start prior (prior || closing)
  | next {start first last : Nat} (prior closing result : Bool) :
      Delimited bytes start stop listSpace first → first < stop →
      ConnectionTokenGrammar bytes first stop closing last → last < stop →
      ConnectionListGrammar bytes stop (last + 1) (prior || closing) result →
      ConnectionListGrammar bytes stop start prior result

theorem connectionList_sound (bytes : ByteArray) (start stop : Nat) (prior result : Bool)
    (hs : start ≤ stop) (hb : stop ≤ bytes.size)
    (h : connectionList bytes start stop prior = .ok result) :
    ConnectionListGrammar bytes stop start prior result := by
  have fs := spanEnd_spec bytes stop listSpace start hs
  rw [connectionList] at h
  split at h
  · rename_i hend
    have he : spanEnd bytes stop listSpace start = stop := by omega
    cases h
    exact .empty prior (by simpa [he, Delimited] using fs)
  · rename_i hfirst
    cases ht : connectionToken bytes (spanEnd bytes stop listSpace start) stop with
    | error status => simp [ht] at h
    | ok pair =>
      obtain ⟨closing, last⟩ := pair
      have tg := connectionToken_sound bytes _ stop closing last fs.2.1 hb ht
      simp only [ht] at h
      split at h
      · rename_i hend
        have lastBound := tg.choose_spec.2.2.1
        have he : last = stop := by omega
        subst last
        cases h
        exact .last prior closing fs (by omega) tg
      · rename_i hend
        split at h
        · contradiction
        · exact .next prior closing result fs (by omega) tg (by omega)
            (connectionList_sound bytes (last + 1) stop (prior || closing) result (by omega) hb h)
termination_by stop - start

theorem connectionList_complete (bytes : ByteArray) (stop : Nat) (hb : stop ≤ bytes.size)
    (start : Nat) (prior result : Bool) (h : ConnectionListGrammar bytes stop start prior result) :
    connectionList bytes start stop prior = .ok result := by
  induction h with
  | @empty start closing span =>
    have scan := (delimited_iff bytes start stop stop listSpace (by have := span.1; omega)).mp span
    rw [connectionList]
    simp [scan]
  | @last start first prior closing span bound tok =>
    have scan := (delimited_iff bytes start stop first listSpace (by have := span.1; omega)).mp span
    have parsed := connectionToken_complete bytes first stop closing stop tok
    rw [connectionList]
    simp [scan, show ¬ first ≥ stop by omega, parsed]
  | @next start first last prior closing result span bound tok lastBound tail ih =>
    have scan := (delimited_iff bytes start stop first listSpace (by have := span.1; omega)).mp span
    have parsed := connectionToken_complete bytes first stop closing last tok
    obtain ⟨nameEnd, name, ws, _, _, _⟩ := tok
    have before := span.1
    have firstName := name.1
    have nameLast := ws.1
    rw [connectionList]
    simp [scan, show ¬ first ≥ stop by omega, parsed, show ¬ last ≥ stop by omega,
      show ¬ last < start by omega, ih]

theorem connectionOptions_iff (bytes : ByteArray) (start stop : Nat) (result : Bool) :
    connectionOptions bytes start stop = .ok result ↔
      start ≤ stop ∧ stop ≤ bytes.size ∧ ConnectionListGrammar bytes stop start false result := by
  unfold connectionOptions
  by_cases hs : start ≤ stop
  · by_cases hb : stop ≤ bytes.size
    · simp only [hs, hb, decide_true, Bool.and_self, ↓reduceIte, true_and]
      exact ⟨connectionList_sound bytes start stop false result hs hb,
        connectionList_complete bytes stop hb start false result⟩
    · simp [hb]
  · simp [hs]

/-- Transfer-parameter ABNF with literal delimiters and bounded lexical spans.
The predicates quantify over octets; none calls the parameter parser. Token
maximality is just the boundary between the token and the following production. -/
def TransferParameterGrammar (bytes : ByteArray) (start stop last : Nat) : Prop :=
  start < stop ∧ stop ≤ bytes.size ∧ bytes[start]! = 59 ∧
  ∃ key nameEnd eq value,
    Delimited bytes (start + 1) stop space key ∧
    Delimited bytes key stop token nameEnd ∧ key < nameEnd ∧
    Delimited bytes nameEnd stop space eq ∧ eq < stop ∧ bytes[eq]! = 61 ∧
    Delimited bytes (eq + 1) stop space value ∧
    (QuotedGrammar bytes value stop last ∨
      (Delimited bytes value stop token last ∧ value < last))

theorem transferParameter_sound (bytes : ByteArray) (start stop last : Nat)
    (hb : stop ≤ bytes.size) (h : transferParameter bytes start stop = some last) :
    TransferParameterGrammar bytes start stop last := by
  unfold transferParameter at h
  split at h
  · contradiction
  · rename_i hs
    have bounds : start < stop ∧ bytes[start]! = 59 := by simpa using hs
    have key := spanEnd_spec bytes stop space (start + 1) (by omega)
    have name := spanEnd_spec bytes stop token _ key.2.1
    have eq := spanEnd_spec bytes stop space _ name.2.1
    dsimp only at h
    split at h
    · contradiction
    · rename_i hn
      have ok : spanEnd bytes stop token (spanEnd bytes stop space (start + 1)) ≠
          spanEnd bytes stop space (start + 1) ∧
          spanEnd bytes stop space (spanEnd bytes stop token (spanEnd bytes stop space (start + 1))) < stop ∧
          bytes[spanEnd bytes stop space (spanEnd bytes stop token (spanEnd bytes stop space (start + 1)))]! = 61 := by
        simpa [and_assoc] using hn
      have value := spanEnd_spec bytes stop space
        (spanEnd bytes stop space (spanEnd bytes stop token (spanEnd bytes stop space (start + 1))) + 1) (by omega)
      refine ⟨bounds.1, hb, bounds.2, _, _, _, _, key, name, by omega, eq, ok.2.1, ok.2.2, value, ?_⟩
      try dsimp only at h
      split at h
      · exact Or.inl ((quotedEnd_iff _ _ _ _).mp h)
      · have lastSpan := spanEnd_spec bytes stop token _ value.2.1
        split at h
        · contradiction
        · rename_i hnlast
          cases h
          exact Or.inr ⟨lastSpan, by simp only [beq_iff_eq] at hnlast; omega⟩

theorem transferParameter_complete (bytes : ByteArray) (start stop last : Nat)
    (h : TransferParameterGrammar bytes start stop last) :
    transferParameter bytes start stop = some last := by
  obtain ⟨hs, hb, semi, key, nameEnd, eq, value, keyG, nameG, hn, eqG, he, equals, valueG, val⟩ := h
  have keyScan := (delimited_iff bytes (start + 1) stop key space (by omega)).mp keyG
  have nameScan := (delimited_iff bytes key stop nameEnd token keyG.2.1).mp nameG
  have eqScan := (delimited_iff bytes nameEnd stop eq space nameG.2.1).mp eqG
  have valueScan := (delimited_iff bytes (eq + 1) stop value space (by omega)).mp valueG
  have hn' : nameEnd ≠ key := by omega
  unfold transferParameter
  simp only [show ¬ start ≥ stop by omega, decide_false, semi, bne_self_eq_false,
    Bool.or_self, Bool.false_eq_true, ↓reduceIte, keyScan, nameScan, eqScan]
  simp only [show (nameEnd == key) = false by simp [hn'], show ¬ eq ≥ stop by omega,
    decide_false, equals, bne_self_eq_false, Bool.or_self, Bool.false_eq_true, ↓reduceIte, valueScan]
  rcases val with quoted | ⟨tokenSpan, hlast⟩
  · have parsed := (quotedEnd_iff bytes value stop last).mpr quoted
    simp [quoted.1, quoted.2.2.1, parsed, -getElem!_pos]
  · have scan := (delimited_iff bytes value stop last token valueG.2.1).mp tokenSpan
    have startToken := tokenSpan.2.2.1 value (by omega) hlast
    have noQuote : bytes[value]! ≠ 34 := by intro hq; simp [hq, token] at startToken
    simp [noQuote, scan, show last ≠ value by omega]

theorem transferParameter_iff (bytes : ByteArray) (start stop last : Nat) (hb : stop ≤ bytes.size) :
    transferParameter bytes start stop = some last ↔ TransferParameterGrammar bytes start stop last :=
  ⟨transferParameter_sound bytes start stop last hb, transferParameter_complete bytes start stop last⟩

theorem transferParameter_bounds (bytes : ByteArray) (start stop last : Nat)
    (h : TransferParameterGrammar bytes start stop last) : start < last ∧ last ≤ stop := by
  obtain ⟨_, _, _, key, nameEnd, eq, value, keyG, nameG, hn, eqG, he, _, valueG, val⟩ := h
  have hk := keyG.1
  have hne := eqG.1
  have hv := valueG.1
  rcases val with q | ⟨t, hlast⟩
  · have bounds := quotedTail_bounds bytes stop (value + 1) last q.2.2.2
    omega
  · have bound := t.2.1
    omega

/-- Zero or more transfer parameters and trailing OWS; the final delimiter is
only a comma or field end. Chunked's parameter prohibition is explicit. -/
inductive TransferParametersGrammar (bytes : ByteArray) (stop : Nat) (chunked : Bool) : Nat → Nat → Prop where
  | finish {start last : Nat} : Delimited bytes start stop space last →
      (last = stop ∨ bytes[last]! = 44) → TransferParametersGrammar bytes stop chunked start last
  | next {start semi next last : Nat} : Delimited bytes start stop space semi →
      chunked = false → TransferParameterGrammar bytes semi stop next →
      TransferParametersGrammar bytes stop chunked next last →
      TransferParametersGrammar bytes stop chunked start last

theorem transferParameters_sound (bytes : ByteArray) (start stop last : Nat) (chunked : Bool)
    (hs : start ≤ stop) (hb : stop ≤ bytes.size)
    (h : transferParameters bytes start stop chunked = some last) :
    TransferParametersGrammar bytes stop chunked start last := by
  rw [transferParameters] at h
  split at h
  · rename_i hend
    have he : start = stop := by omega
    subst start
    cases h
    exact .finish ⟨Nat.le_refl _, Nat.le_refl _, (by intro i hi hj; omega), Or.inl rfl⟩ (Or.inl rfl)
  · rename_i hstart
    have span := spanEnd_spec bytes stop space start hs
    dsimp only at h
    split at h
    · rename_i hend
      cases h
      apply TransferParametersGrammar.finish span
      have hd : spanEnd bytes stop space start ≥ stop ∨ bytes[spanEnd bytes stop space start]! = 44 := by simpa using hend
      rcases hd with hd | hd
      · exact Or.inl (by omega)
      · exact Or.inr hd
    · split at h
      · contradiction
      · rename_i hc
        cases hp : transferParameter bytes (spanEnd bytes stop space start) stop with
        | none => simp [hp] at h
        | some next =>
          have grammar := transferParameter_sound bytes _ stop next hb hp
          have bound := transferParameter_bounds bytes _ stop next grammar
          simp only [hp] at h
          split at h
          · contradiction
          · exact .next span (Bool.eq_false_iff.mpr hc) grammar
              (transferParameters_sound bytes next stop last chunked bound.2 hb h)
termination_by stop - start

theorem transferParameters_bounds (bytes : ByteArray) (stop start last : Nat) (chunked : Bool)
    (h : TransferParametersGrammar bytes stop chunked start last) :
    start ≤ last ∧ last ≤ stop ∧ (last = stop ∨ bytes[last]! = 44) := by
  induction h with
  | finish span delim => exact ⟨span.1, span.2.1, delim⟩
  | @next start semi next last span hc param tail ih =>
    have hp := transferParameter_bounds bytes semi stop next param
    have hs := span.1
    exact ⟨by omega, ih.2⟩

theorem transferParameters_complete (bytes : ByteArray) (stop : Nat) (chunked : Bool)
    (start last : Nat) (h : TransferParametersGrammar bytes stop chunked start last) :
    transferParameters bytes start stop chunked = some last := by
  induction h with
  | @finish start last span delim =>
    have hs := span.1
    have hl := span.2.1
    have scan := (delimited_iff bytes start stop last space (by omega)).mp span
    rw [transferParameters]
    by_cases hstart : start ≥ stop
    · have he : start = last := by omega
      simp only [hstart, ↓reduceIte, Option.some.injEq]
      exact he
    · simp only [hstart, ↓reduceIte, scan]
      rcases delim with hd | hd <;> simp [hd]
  | @next start semi next last span hc param tail ih =>
    have hs := span.1
    have hp := transferParameter_bounds bytes semi stop next param
    have bounds := param.1
    have bsemi := param.2.2.1
    have scan := (delimited_iff bytes start stop semi space (by omega)).mp span
    have parsed := transferParameter_complete bytes semi stop next param
    simp only [hc] at ih
    rw [transferParameters]
    simp [show ¬ start ≥ stop by omega, scan, show ¬ semi ≥ stop by omega, bsemi, hc, parsed,
      show ¬ next ≤ start by omega, ih, -getElem!_pos]

theorem transferParameters_iff (bytes : ByteArray) (start stop last : Nat) (chunked : Bool)
    (hs : start ≤ stop) (hb : stop ≤ bytes.size) :
    transferParameters bytes start stop chunked = some last ↔
      TransferParametersGrammar bytes stop chunked start last :=
  ⟨transferParameters_sound bytes start stop last chunked hs hb,
    transferParameters_complete bytes stop chunked start last⟩

/-- A nonempty coding token and its parameter sequence, preserving its exact
case-insensitive classification. Only the 'chunked' coding is implemented. -/
def TransferCodingGrammar (bytes : ByteArray) (start stop : Nat) (chunked : Bool) (last : Nat) : Prop :=
  ∃ nameEnd, Delimited bytes start stop token nameEnd ∧ start < nameEnd ∧
    chunked = equals bytes start nameEnd "chunked" true ∧
    TransferParametersGrammar bytes stop chunked nameEnd last

theorem transferCoding_sound (bytes : ByteArray) (start stop : Nat) (chunked : Bool) (last : Nat)
    (hs : start ≤ stop) (hb : stop ≤ bytes.size)
    (h : transferCoding bytes start stop = .ok (chunked, last)) :
    TransferCodingGrammar bytes start stop chunked last := by
  have name := spanEnd_spec bytes stop token start hs
  unfold transferCoding at h
  dsimp only at h
  split at h
  · contradiction
  · rename_i hn
    cases hp : transferParameters bytes (spanEnd bytes stop token start) stop
        (equals bytes start (spanEnd bytes stop token start) "chunked" true) with
    | none => simp [hp] at h
    | some value =>
      simp only [hp] at h
      cases h
      exact ⟨_, name, by simp only [beq_iff_eq] at hn; omega, rfl,
        transferParameters_sound bytes _ stop _ _ name.2.1 hb hp⟩

theorem transferCoding_complete (bytes : ByteArray) (start stop : Nat) (chunked : Bool) (last : Nat)
    (h : TransferCodingGrammar bytes start stop chunked last) :
    transferCoding bytes start stop = .ok (chunked, last) := by
  obtain ⟨nameEnd, name, hn, rfl, parameters⟩ := h
  have hs := name.2.1
  have scan := (delimited_iff bytes start stop nameEnd token (by omega)).mp name
  have parsed := transferParameters_complete bytes stop _ nameEnd last parameters
  simp [transferCoding, scan, show nameEnd ≠ start by omega, parsed]

theorem transferCoding_iff (bytes : ByteArray) (start stop : Nat) (chunked : Bool) (last : Nat)
    (hs : start ≤ stop) (hb : stop ≤ bytes.size) :
    transferCoding bytes start stop = .ok (chunked, last) ↔
      TransferCodingGrammar bytes start stop chunked last :=
  ⟨transferCoding_sound bytes start stop chunked last hs hb,
    transferCoding_complete bytes start stop chunked last⟩

theorem transferCoding_bounds (bytes : ByteArray) (start stop : Nat) (chunked : Bool) (last : Nat)
    (h : TransferCodingGrammar bytes start stop chunked last) :
    start < last ∧ last ≤ stop ∧ (last = stop ∨ bytes[last]! = 44) := by
  obtain ⟨nameEnd, _, hn, _, parameters⟩ := h
  have bounds := transferParameters_bounds bytes stop nameEnd last chunked parameters
  exact ⟨by omega, bounds.2⟩

/-- Complete Transfer-Encoding recipient list semantics. The previous coding
must not be chunked before another nonempty member. Empty members do not change
state. Unsupported is accumulated over every non-chunked coding. -/
inductive TransferListGrammar (bytes : ByteArray) (stop : Nat) :
    Nat → Bool → Bool → (Bool × Bool) → Prop where
  | empty {start : Nat} (chunked unsupported : Bool) :
      Delimited bytes start stop listSpace stop →
      TransferListGrammar bytes stop start chunked unsupported (chunked, unsupported)
  | last {start first : Nat} (unsupported chunked : Bool) :
      Delimited bytes start stop listSpace first → first < stop →
      TransferCodingGrammar bytes first stop chunked stop →
      TransferListGrammar bytes stop start false unsupported (chunked, unsupported || !chunked)
  | next {start first last : Nat} (unsupported chunked : Bool) (result : Bool × Bool) :
      Delimited bytes start stop listSpace first → first < stop →
      TransferCodingGrammar bytes first stop chunked last → last < stop →
      TransferListGrammar bytes stop (last + 1) chunked (unsupported || !chunked) result →
      TransferListGrammar bytes stop start false unsupported result

theorem transferList_sound (bytes : ByteArray) (start stop : Nat) (chunked unsupported : Bool)
    (result : Bool × Bool) (hs : start ≤ stop) (hb : stop ≤ bytes.size)
    (h : transferList bytes start stop chunked unsupported = .ok result) :
    TransferListGrammar bytes stop start chunked unsupported result := by
  have span := spanEnd_spec bytes stop listSpace start hs
  rw [transferList] at h
  split at h
  · rename_i hend
    have he : spanEnd bytes stop listSpace start = stop := by omega
    cases h
    exact .empty chunked unsupported (by simpa [he, Delimited] using span)
  · rename_i hfirst
    split at h
    · contradiction
    · rename_i hc
      have hc' : chunked = false := Bool.eq_false_iff.mpr hc
      subst chunked
      cases ht : transferCoding bytes (spanEnd bytes stop listSpace start) stop with
      | error status => simp [ht] at h
      | ok pair =>
        obtain ⟨chunked, last⟩ := pair
        have tg := transferCoding_sound bytes _ stop chunked last span.2.1 hb ht
        have bounds := transferCoding_bounds bytes _ stop chunked last tg
        simp only [ht] at h
        split at h
        · rename_i hend
          have he : last = stop := by omega
          subst last
          cases h
          exact .last unsupported chunked span (by omega) tg
        · rename_i hend
          split at h
          · contradiction
          · exact .next unsupported chunked result span (by omega) tg (by omega)
              (transferList_sound bytes (last + 1) stop chunked (unsupported || !chunked) result
                (by omega) hb h)
termination_by stop - start

theorem transferList_complete (bytes : ByteArray) (stop start : Nat) (chunked unsupported : Bool)
    (result : Bool × Bool) (h : TransferListGrammar bytes stop start chunked unsupported result) :
    transferList bytes start stop chunked unsupported = .ok result := by
  induction h with
  | @empty start chunked unsupported span =>
    have hs := span.1
    have scan := (delimited_iff bytes start stop stop listSpace (by omega)).mp span
    rw [transferList]
    simp [scan]
  | @last start first unsupported chunked span hf coding =>
    have hs := span.1
    have scan := (delimited_iff bytes start stop first listSpace (by omega)).mp span
    have parsed := transferCoding_complete bytes first stop chunked stop coding
    rw [transferList]
    simp [scan, show ¬ first ≥ stop by omega, parsed]
  | @next start first last unsupported chunked result span hf coding hl tail ih =>
    have hs := span.1
    have bounds := transferCoding_bounds bytes first stop chunked last coding
    have scan := (delimited_iff bytes start stop first listSpace (by omega)).mp span
    have parsed := transferCoding_complete bytes first stop chunked last coding
    rw [transferList]
    simp [scan, show ¬ first ≥ stop by omega, parsed, show ¬ last ≥ stop by omega,
      show ¬ last < start by omega, ih]

/-- Exact field-level grammar and state result, including repeated header lines,
ignored empty members, arbitrary extension parameters, and chunked ordering. -/
theorem transferCodings_iff (bytes : ByteArray) (start stop : Nat) (previousChunked : Bool)
    (result : Bool × Bool) :
    transferCodings bytes start stop previousChunked = .ok result ↔
      start ≤ stop ∧ stop ≤ bytes.size ∧ TransferListGrammar bytes stop start previousChunked false result := by
  unfold transferCodings
  by_cases hs : start ≤ stop
  · by_cases hb : stop ≤ bytes.size
    · simp only [hs, hb, decide_true, Bool.and_self, ↓reduceIte, true_and]
      exact ⟨transferList_sound bytes start stop previousChunked false result hs hb,
        transferList_complete bytes stop start previousChunked false result⟩
    · simp [hb]
  · simp [hs]

end FastHTTP.Protocol
