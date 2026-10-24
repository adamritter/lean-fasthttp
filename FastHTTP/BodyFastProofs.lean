import FastHTTP.BodyProofs

namespace FastHTTP.Protocol

theorem payload_push_fold (xs : List UInt8) (body : ByteArray) :
    xs.foldl ByteArray.push body = body ++ xs.toByteArray := by
  induction xs generalizing body with
  | nil => simp
  | cons b xs ih =>
    rw [List.foldl_cons, ih]
    rw [← ByteArray.append_toByteArray_singleton, ByteArray.append_assoc, ← List.toByteArray_append]
    rfl

theorem bodyList_fixed_partial (cfg : Config) (xs : List UInt8) (s : BodyState) (count extra : Nat) :
    xs.foldl (bodyAdvance cfg) ⟨.more { s with phase := .fixed (xs.length + extra + 1) }, count⟩ =
      ⟨.more { s with phase := .fixed (extra + 1), body := xs.foldl ByteArray.push s.body }, count + xs.length⟩ := by
  induction xs generalizing s count with
  | nil => simp
  | cons b xs ih =>
    have step : bodyAdvance cfg
        ⟨.more { s with phase := .fixed ((b :: xs).length + extra + 1) }, count⟩ b =
        ⟨.more { s with phase := .fixed (xs.length + extra + 1), body := s.body.push b }, count + 1⟩ := by
      have hnot : extra + (xs.length + 2) ≠ 1 := by omega
      simp [bodyAdvance, bodyByte, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, hnot]
    rw [List.foldl_cons, step]
    simpa [List.foldl_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      ih { s with body := s.body.push b } (count + 1)

theorem bodyList_data_payload (cfg : Config) (xs : List UInt8) (s : BodyState) (count extra : Nat)
    (hne : xs ≠ []) :
    xs.foldl (bodyAdvance cfg) ⟨.more { s with phase := .data (xs.length + extra) }, count⟩ =
      ⟨.more { s with
        phase := if extra == 0 then .dataCR else .data extra
        body := xs.foldl ByteArray.push s.body }, count + xs.length⟩ := by
  induction xs generalizing s count with
  | nil => contradiction
  | cons b xs ih =>
    cases xs with
    | nil =>
      simp [bodyAdvance, bodyByte, List.foldl_cons, Nat.add_comm]
    | cons c xs =>
      have step : bodyAdvance cfg
          ⟨.more { s with phase := .data ((b :: c :: xs).length + extra) }, count⟩ b =
          ⟨.more { s with phase := .data ((c :: xs).length + extra), body := s.body.push b }, count + 1⟩ := by
        have hnot : extra + (xs.length + 2) ≠ 1 := by omega
        simp [bodyAdvance, bodyByte, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, hnot]
      rw [List.foldl_cons, step]
      simpa [List.foldl_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih { s with body := s.body.push b } (count + 1) (by simp)

theorem payload_toByteArray (bytes : ByteArray) : bytes.data.toList.toByteArray = bytes := by
  ext1
  simp

theorem bodyBulk_fixed (cfg : Config) (s : BodyState) (remaining count : Nat) (piece : ByteArray)
    (hsize : piece.size ≤ remaining + 1) :
    bodyBulk ⟨.more { s with phase := .fixed (remaining + 1) }, count⟩ piece =
      bodyFold cfg ⟨.more { s with phase := .fixed (remaining + 1) }, count⟩ piece := by
  by_cases he : piece.size = remaining + 1
  · have exactBody := bodyList_fixed_exact cfg piece.data.toList s count
    rw [payload_push_fold, payload_toByteArray] at exactBody
    simpa [bodyFold, Array.foldl_toList, bodyInitial, bodyBulk, he] using exactBody.symm
  · have hn : piece.size ≤ remaining := by omega
    have total : piece.size + (remaining - piece.size) + 1 = remaining + 1 := by omega
    have left : remaining + 1 - piece.size = remaining - piece.size + 1 := by omega
    have part := bodyList_fixed_partial cfg piece.data.toList s count (remaining - piece.size)
    rw [payload_push_fold, payload_toByteArray] at part
    simpa [bodyFold, Array.foldl_toList, bodyBulk, he, total, left, payload_push_fold, payload_toByteArray] using part.symm

theorem bodyBulk_data (cfg : Config) (s : BodyState) (remaining count : Nat) (piece : ByteArray)
    (hsize : piece.size ≤ remaining + 1) (hne : 0 < piece.size) :
    bodyBulk ⟨.more { s with phase := .data (remaining + 1) }, count⟩ piece =
      bodyFold cfg ⟨.more { s with phase := .data (remaining + 1) }, count⟩ piece := by
  have total : piece.size + (remaining + 1 - piece.size) = remaining + 1 := by omega
  have hl : piece.data.toList ≠ [] := by
    intro h
    have hz : piece.size = 0 := by simpa using congrArg List.length h
    omega
  have part := bodyList_data_payload cfg piece.data.toList s count (remaining + 1 - piece.size) hl
  rw [payload_push_fold, payload_toByteArray] at part
  by_cases he : piece.size = remaining + 1
  · simpa [bodyFold, Array.foldl_toList, bodyBulk, he, payload_push_fold, payload_toByteArray] using part.symm
  · have hz : remaining + 1 - piece.size ≠ 0 := by omega
    simpa [bodyFold, Array.foldl_toList, bodyBulk, he, total, hz, payload_push_fold, payload_toByteArray] using part.symm

/-- Splitting the input at any valid cursor preserves the byte-machine fold. -/
theorem bodyLoop_split (cfg : Config) (bytes : ByteArray) (start stop : Nat) (s : BodyScan)
    (h : start ≤ stop) :
    bodyLoop cfg bytes start s =
      bodyLoop cfg bytes stop (bodyFold cfg s (bytes.extract start stop)) := by
  rw [bodyLoop_eq_fold, bodyLoop_eq_fold]
  simp only [bodyFold, ← Array.foldl_toList, ByteArray.data_extract, Array.toList_extract, List.extract]
  have hd : bytes.data.toList.drop stop = (bytes.data.toList.drop start).drop (stop - start) := by
    rw [List.drop_drop]
    congr 1
    omega
  rw [hd, ← List.foldl_append, List.take_append_drop]

theorem bodyBulk_refines (cfg : Config) (s : BodyScan) (state : BodyState)
    (remaining : Nat) (piece : ByteArray) (ha : s.action = .more state)
    (hp : state.phase = .fixed (remaining + 1) ∨ state.phase = .data (remaining + 1))
    (hsize : piece.size ≤ remaining + 1) (hne : 0 < piece.size) :
    bodyBulk s piece = bodyFold cfg s piece := by
  cases s with
  | mk action count =>
    simp only at ha
    subst action
    rcases hp with hp | hp
    · have same : { state with phase := .fixed (remaining + 1) } = state := by cases state; simp_all
      simpa [same] using bodyBulk_fixed cfg state remaining count piece hsize
    · have same : { state with phase := .data (remaining + 1) } = state := by cases state; simp_all
      simpa [same] using bodyBulk_data cfg state remaining count piece hsize hne

/-- The optimized runtime loop equals the full byte automaton for every buffer,
state and cursor. There is no unchecked replacement or implementation axiom. -/
theorem bodyFastLoop_eq_bodyLoop (cfg : Config) (bytes : ByteArray) (i : Nat) (s : BodyScan) :
    bodyFastLoop cfg bytes i s = bodyLoop cfg bytes i s := by
  rw [bodyFastLoop]
  split
  next hi =>
    split
    next state hs =>
      split
      next remaining hp =>
        let stop := i + min (remaining + 1) (bytes.size - i)
        have hsz : (bytes.extract i stop).size = min (remaining + 1) (bytes.size - i) := by
          simp only [ByteArray.size_extract, stop]
          omega
        have bulk := bodyBulk_refines cfg s state remaining (bytes.extract i stop) hs (Or.inl hp)
          (by rw [hsz]; omega) (by rw [hsz]; omega)
        rw [bodyFastLoop_eq_bodyLoop, bulk, ← bodyLoop_split cfg bytes i stop s (by dsimp [stop]; omega)]
      next remaining hp =>
        let stop := i + min (remaining + 1) (bytes.size - i)
        have hsz : (bytes.extract i stop).size = min (remaining + 1) (bytes.size - i) := by
          simp only [ByteArray.size_extract, stop]
          omega
        have bulk := bodyBulk_refines cfg s state remaining (bytes.extract i stop) hs (Or.inr hp)
          (by rw [hsz]; omega) (by rw [hsz]; omega)
        rw [bodyFastLoop_eq_bodyLoop, bulk, ← bodyLoop_split cfg bytes i stop s (by dsimp [stop]; omega)]
      next hp =>
        rw [bodyFastLoop_eq_bodyLoop]
        conv =>
          rhs
          rw [bodyLoop]
        simp only [hs, dite_eq_left hi]
    next ht =>
      have terminal : BodyTerminal s := by cases ha : s.action <;> simp_all [BodyTerminal]
      rw [bodyLoop_eq_fold, bodyList_terminal cfg s _ terminal]
  next hi =>
    rw [bodyLoop_eq_fold, List.drop_eq_nil_of_le (by simpa using Nat.le_of_not_gt hi)]
    rfl
termination_by bytes.size - i
decreasing_by all_goals simp_wf; omega

/-- End-to-end refinement of the actual public decoder. -/
theorem decodeBody_eq_reference (cfg : Config) (bytes : ByteArray) (start : Nat) (initial : BodyState) :
    decodeBody cfg bytes start initial = decodeBodyReference cfg bytes start initial := by
  simp only [decodeBody, decodeBodyReference, bodyFastLoop_eq_bodyLoop]

theorem decodeBody_fragmentation (cfg : Config) (initial : BodyState) (a b : ByteArray) :
    decodeBody cfg (a ++ b) 0 initial =
      match decodeBody cfg a 0 initial with
      | .need next => shiftBodyResult a.size (decodeBody cfg b 0 next)
      | terminal => terminal := by
  simp only [decodeBody_eq_reference]
  exact decodeBodyReference_fragmentation cfg initial a b

theorem decodeBody_done_bounds (cfg : Config) (bytes : ByteArray) (start : Nat)
    (initial : BodyState) (body : ByteArray) (trailers : Array (String × ByteArray)) (stop : Nat)
    (hs : start ≤ bytes.size) (hd : decodeBody cfg bytes start initial = .done body trailers stop) :
    start ≤ stop ∧ stop ≤ bytes.size := by
  exact decodeBodyReference_done_bounds cfg bytes start initial body trailers stop hs
    (by simpa only [decodeBody_eq_reference] using hd)

theorem decodeBody_partition (cfg : Config) (bytes : ByteArray) (start : Nat)
    (initial : BodyState) (body : ByteArray) (trailers : Array (String × ByteArray)) (stop : Nat)
    (hs : start ≤ bytes.size) (hd : decodeBody cfg bytes start initial = .done body trailers stop) :
    bytes.extract start stop ++ bytes.extract stop bytes.size = bytes.extract start bytes.size := by
  exact decodeBodyReference_partition cfg bytes start initial body trailers stop hs
    (by simpa only [decodeBody_eq_reference] using hd)

/-- The production decoder returns exactly Content-Length payload octets and
leaves an arbitrary following message untouched. -/
theorem decodeBody_fixed_exact (cfg : Config) (payload suffix : ByteArray) (s : BodyState) :
    decodeBody cfg (payload ++ suffix) 0 { s with phase := .fixed payload.size } =
      .done (s.body ++ payload) s.trailers payload.size := by
  rw [decodeBody_eq_reference]
  change (bodyFeed cfg (bodyInitial { s with phase := .fixed payload.size }) (payload ++ suffix)).result = _
  rw [bodyFeed_fixed_exact]
  simp only [BodyScan.result, ← Array.foldl_toList, payload_push_fold, payload_toByteArray]

/-- Once the real decoder completes a message, appending any wire suffix cannot
change its body, trailers, or stop cursor. -/
theorem decodeBody_pipeline_suffix (cfg : Config) (initial : BodyState) (first suffix body : ByteArray)
    (trailers : Array (String × ByteArray)) (stop : Nat)
    (h : decodeBody cfg first 0 initial = .done body trailers stop) :
    decodeBody cfg (first ++ suffix) 0 initial = .done body trailers stop := by
  rw [decodeBody_fragmentation, h]

end FastHTTP.Protocol
