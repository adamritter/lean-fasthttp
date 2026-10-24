import FastHTTP.ChunkGrammarProofs

namespace FastHTTP.Protocol

/-- The reverse whitespace scan keeps exactly the non-whitespace suffix boundary. -/
theorem trimEnd_spec (bytes : ByteArray) (start stop : Nat) (hs : start ≤ stop) :
    let last := trimEnd bytes start stop
    start ≤ last ∧ last ≤ stop ∧ Octets bytes SpaceOctet last stop ∧
      (last = start ∨ space bytes[last - 1]! = false) := by
  rw [trimEnd]
  split
  · rename_i h
    have hh : start < stop ∧ space bytes[stop - 1]! = true := by simpa using h
    have ih := trimEnd_spec bytes start (stop - 1) (by omega)
    refine ⟨ih.1, by omega, ?_, ih.2.2.2⟩
    intro i hi hj
    by_cases he : i = stop - 1
    · simpa [he] using (space_iff _).mp hh.2
    · exact ih.2.2.1 i hi (by omega)
  · rename_i h
    refine ⟨hs, by omega, ?_, ?_⟩
    · intro i hi hj; omega
    · by_cases he : stop = start
      · exact Or.inl he
      · right
        cases hb : space bytes[stop - 1]! <;> simp_all <;> omega
termination_by stop

/-- Exact optional-whitespace removal with all original interior octets kept. -/
def Trimmed (bytes : ByteArray) (start stop first last : Nat) : Prop :=
  start ≤ first ∧ first ≤ last ∧ last ≤ stop ∧
  Octets bytes SpaceOctet start first ∧ Octets bytes SpaceOctet last stop ∧
  (first = last ∨ (space bytes[first]! = false ∧ space bytes[last - 1]! = false))

theorem trimSpan_spec (bytes : ByteArray) (start stop : Nat) (hs : start ≤ stop) :
    Trimmed bytes start stop (spanEnd bytes stop space start)
      (trimEnd bytes (spanEnd bytes stop space start) stop) := by
  have first := spanEnd_spec bytes stop space start hs
  have last := trimEnd_spec bytes (spanEnd bytes stop space start) stop first.2.1
  refine ⟨first.1, last.1, last.2.1, ?_, last.2.2.1, ?_⟩
  · intro i hi hj; exact (space_iff _).mp (first.2.2.1 i hi hj)
  · by_cases he : spanEnd bytes stop space start = trimEnd bytes (spanEnd bytes stop space start) stop
    · exact Or.inl he
    · right
      rcases first.2.2.2 with hf | hf
      · exfalso; omega
      · rcases last.2.2.2 with hl | hl
        · exfalso; omega
        · exact ⟨hf, hl⟩

theorem trimEnd_complete (bytes : ByteArray) (start stop last : Nat)
    (hs : start ≤ last) (hl : last ≤ stop) (ws : Octets bytes SpaceOctet last stop)
    (he : last = start ∨ space bytes[last - 1]! = false) :
    trimEnd bytes start stop = last := by
  have actual := trimEnd_spec bytes start stop (by omega)
  by_cases hr : trimEnd bytes start stop = last
  · exact hr
  · exfalso
    by_cases hlt : trimEnd bytes start stop < last
    · rcases he with he | he
      · omega
      · have ha := (space_iff _).mpr (actual.2.2.1 (last - 1) (by omega) (by omega))
        simp [he] at ha
    · rcases actual.2.2.2 with ha | ha
      · omega
      · have hb := (space_iff _).mpr (ws (trimEnd bytes start stop - 1) (by omega) (by omega))
        simp [ha] at hb

/-- A grammar-specified trimmed slice equals the executable trim result,
including an all-whitespace field with an empty retained value. -/
theorem trimSpan_exact (bytes : ByteArray) (start stop first last : Nat)
    (h : Trimmed bytes start stop first last) :
    bytes.extract (spanEnd bytes stop space start)
      (trimEnd bytes (spanEnd bytes stop space start) stop) = bytes.extract first last := by
  obtain ⟨hs, hf, hl, leading, trailing, edge⟩ := h
  rcases edge with he | ⟨hfirst, hlast⟩
  · subst last
    have ha : Octets bytes (fun b => space b = true) start stop := by
      intro i hi hj
      by_cases hif : i < first
      · exact (space_iff _).mpr (leading i hi hif)
      · exact (space_iff _).mpr (trailing i (by omega) hj)
    have scan := spanEnd_complete bytes stop space start stop (by omega) (by omega) ha (Or.inl rfl)
    simp [scan, trimEnd]
  · have scan := spanEnd_complete bytes stop space start first hs (by omega)
      (fun i hi hj => (space_iff _).mpr (leading i hi hj)) (Or.inr hfirst)
    have trim := trimEnd_complete bytes first stop last hf hl trailing (Or.inr hlast)
    rw [scan, trim]

/-- Independent trailer field-line envelope plus the explicit disallowed-name
policy and the exact original name/value slices returned to the application. -/
def TrailerGrammar (line : ByteArray) (field : String × ByteArray) : Prop :=
  ∃ colon first last,
    TokenGrammar line 0 colon ∧ colon < line.size ∧ line[colon]! = 58 ∧
    Octets line FieldOctet (colon + 1) line.size ∧
    (∀ name ∈ forbiddenTrailers, equals line 0 colon name true = false) ∧
    Trimmed line (colon + 1) line.size first last ∧
    field = (String.fromUTF8! (line.extract 0 colon), line.extract first last)

/-- Every accepted production trailer is a complete RFC field line; framing
and routing fields cannot overwrite headers, and trimming preserves exact bytes. -/
theorem trailer_sound (line : ByteArray) (field : String × ByteArray)
    (h : trailer line = .ok field) : TrailerGrammar line field := by
  unfold trailer at h
  dsimp only at h
  split at h
  · contradiction
  · rename_i hn
    have hc : spanEnd line line.size token 0 ≠ 0 ∧
        spanEnd line line.size token 0 < line.size ∧
        line[spanEnd line line.size token 0]! = 58 := by simpa [and_assoc] using hn
    have name := spanEnd_token line 0 (by omega) hc.1
    split at h
    · contradiction
    · rename_i ha
      have allowed : ∀ name ∈ forbiddenTrailers,
          equals line 0 (spanEnd line line.size token 0) name true = false := by
        simpa using ha
      split at h
      · contradiction
      · rename_i hv
        have hv' : spanEnd line line.size fieldOctet (spanEnd line line.size token 0 + 1) = line.size := by
          simpa using hv
        have value := spanEnd_spec line line.size fieldOctet (spanEnd line line.size token 0 + 1) (by omega)
        cases h
        refine ⟨_, _, _, name, hc.2.1, hc.2.2, ?_, allowed, trimSpan_spec _ _ _ (by omega), rfl⟩
        intro i hi hj
        exact (fieldOctet_iff _).mp (value.2.2.1 i hi (by simpa [hv'] using hj))

/-- Every grammatical trailer admitted by the explicit name policy is accepted,
with exactly the independent grammar's trimmed binary value. -/
theorem trailer_complete (line : ByteArray) (field : String × ByteArray)
    (h : TrailerGrammar line field) : trailer line = .ok field := by
  obtain ⟨colon, first, last, name, hc, hb, value, allowed, trim, out⟩ := h
  dsimp only [TokenGrammar] at name
  have hn := spanEnd_complete line line.size token 0 colon (by omega) (by omega)
    (fun i hi hj => (token_iff _).mpr (name.2.2 i hi hj)) (Or.inr (by simp [hb, token]))
  have hv := spanEnd_complete line line.size fieldOctet (colon + 1) line.size (by omega) (by omega)
    (fun i hi hj => (fieldOctet_iff _).mpr (value i hi hj)) (Or.inl rfl)
  have ha : forbiddenTrailers.any (fun name => equals line 0 colon name true) = false := by
    simpa using allowed
  have ht := trimSpan_exact line (colon + 1) line.size first last trim
  unfold trailer
  simp [hn, show colon ≠ 0 by omega, hc, hb, ha, hv, ht, out, -getElem!_pos]

theorem trailer_iff (line : ByteArray) (field : String × ByteArray) :
    trailer line = .ok field ↔ TrailerGrammar line field :=
  ⟨trailer_sound line field, trailer_complete line field⟩

end FastHTTP.Protocol
