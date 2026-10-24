import FastHTTP.Proofs

/-! Proofs about the complete executable body state machine, for arbitrary input
bytes, including malformed chunk lines and trailers. These establish framing and
fragmentation properties; `chunkSize`/`trailer` lexical RFC correspondence is a
separate obligation, not assumed or asserted by these theorems. -/
namespace FastHTTP.Protocol

/-- Completion and rejection both prevent consumption of subsequent octets. -/
def BodyTerminal (s : BodyScan) : Prop :=
  match s.action with
  | .more _ => False
  | _ => True

theorem bodyAdvance_terminal (cfg : Config) (s : BodyScan) (b : UInt8)
    (h : BodyTerminal s) : bodyAdvance cfg s b = s := by
  cases s with
  | mk action count => cases action <;> simp_all [BodyTerminal, bodyAdvance]

theorem bodyList_terminal (cfg : Config) (s : BodyScan) (xs : List UInt8)
    (h : BodyTerminal s) : xs.foldl (bodyAdvance cfg) s = s := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa [List.foldl_cons, bodyAdvance_terminal cfg s x h] using ih

/-- Early exit in the actual runtime loop refines a fold over all input bytes. -/
theorem bodyLoop_eq_fold (cfg : Config) (bytes : ByteArray) (i : Nat) (s : BodyScan) :
    bodyLoop cfg bytes i s = (bytes.data.toList.drop i).foldl (bodyAdvance cfg) s := by
  rw [bodyLoop]
  split
  next state hs =>
    split
    next hi =>
      rw [List.drop_eq_getElem_cons (by simpa using hi), List.foldl_cons]
      have hb : bytes[i] = bytes.data[i] := ByteArray.getElem_eq_getElem_data
      simp only [Array.getElem_toList]
      rw [← hb]
      exact bodyLoop_eq_fold cfg bytes (i + 1) (bodyAdvance cfg s bytes[i])
    next hi =>
      rw [List.drop_eq_nil_of_le (by simpa using Nat.le_of_not_gt hi)]
      rfl
  next h =>
    exact (bodyList_terminal cfg s _ (by cases hs : s.action <;> simp_all [BodyTerminal])).symm
termination_by bytes.size - i

theorem bodyFeed_eq_fold (cfg : Config) (s : BodyScan) (bytes : ByteArray) :
    bodyFeed cfg s bytes = bodyFold cfg s bytes := by
  simpa [bodyFeed, bodyFold, Array.foldl_toList] using bodyLoop_eq_fold cfg bytes 0 s

/-- Full body decoding is independent of a TCP split, including extensions,
trailers, limits, malformed input, decoded payload and the exact stop offset. -/
theorem bodyFeed_append (cfg : Config) (s : BodyScan) (a b : ByteArray) :
    bodyFeed cfg s (a ++ b) = bodyFeed cfg (bodyFeed cfg s a) b := by
  simp only [bodyFeed_eq_fold, bodyFold, ByteArray.data_append, Array.foldl_append]

theorem bodyFeed_fragments (cfg : Config) (s : BodyScan) (chunks : List ByteArray) :
    chunks.foldl (bodyFeed cfg) s =
      bodyFeed cfg s (chunks.foldl (· ++ ·) ByteArray.empty) := by
  have aux : ∀ (xs : List ByteArray) (acc : ByteArray),
      xs.foldl (bodyFeed cfg) (bodyFeed cfg s acc) =
        bodyFeed cfg s (xs.foldl (· ++ ·) acc) := by
    intro xs
    induction xs with
    | nil => intro acc; rfl
    | cons x xs ih => intro acc; simpa [List.foldl_cons, ← bodyFeed_append] using ih (acc ++ x)
  simpa [bodyFeed_eq_fold, bodyFold] using aux chunks ByteArray.empty

theorem bodyFeed_terminal (cfg : Config) (s : BodyScan) (bytes : ByteArray)
    (h : BodyTerminal s) : bodyFeed cfg s bytes = s := by
  rw [bodyFeed_eq_fold]
  simpa [bodyFold, Array.foldl_toList] using bodyList_terminal cfg s bytes.data.toList h

/-- Appending an arbitrary next request cannot change an already completed body
or its boundary. This includes every suffix, not only generated HTTP examples. -/
theorem bodyFeed_pipeline_suffix (cfg : Config) (s : BodyScan) (first suffix : ByteArray)
    (h : BodyTerminal (bodyFeed cfg s first)) :
    bodyFeed cfg s (first ++ suffix) = bodyFeed cfg s first := by
  rw [bodyFeed_append, bodyFeed_terminal cfg _ suffix h]

theorem bodyAdvance_count_bounds (cfg : Config) (s : BodyScan) (b : UInt8) :
    s.count ≤ (bodyAdvance cfg s b).count ∧ (bodyAdvance cfg s b).count ≤ s.count + 1 := by
  cases s with
  | mk action count => cases action <;> simp [bodyAdvance]

theorem bodyList_count_bounds (cfg : Config) (s : BodyScan) (xs : List UInt8) :
    s.count ≤ (xs.foldl (bodyAdvance cfg) s).count ∧
      (xs.foldl (bodyAdvance cfg) s).count ≤ s.count + xs.length := by
  induction xs generalizing s with
  | nil => simp
  | cons x xs ih =>
    have step := bodyAdvance_count_bounds cfg s x
    have rest := ih (bodyAdvance cfg s x)
    simp only [List.foldl_cons, List.length_cons]
    omega

theorem bodyLoop_count_bounds (cfg : Config) (bytes : ByteArray) (i : Nat) (s : BodyScan) :
    s.count ≤ (bodyLoop cfg bytes i s).count ∧
      (bodyLoop cfg bytes i s).count ≤ s.count + (bytes.size - i) := by
  rw [bodyLoop_eq_fold]
  simpa using bodyList_count_bounds cfg s (bytes.data.toList.drop i)

/-- The public decoder cannot return a cursor outside its input. -/
theorem decodeBodyReference_done_bounds (cfg : Config) (bytes : ByteArray) (start : Nat)
    (initial : BodyState) (body : ByteArray) (trailers : Array (String × ByteArray)) (stop : Nat)
    (hs : start ≤ bytes.size) (hd : decodeBodyReference cfg bytes start initial = .done body trailers stop) :
    start ≤ stop ∧ stop ≤ bytes.size := by
  have bounds := bodyLoop_count_bounds cfg bytes start (bodyInitial initial start)
  simp only [bodyInitial] at bounds
  unfold decodeBodyReference BodyScan.result at hd
  generalize he : bodyLoop cfg bytes start (bodyInitial initial start) = result at hd
  have be := bodyLoop_count_bounds cfg bytes start (bodyInitial initial start)
  rw [he] at be
  simp only [bodyInitial] at be
  cases result with
  | mk action count =>
    cases action <;> simp_all

/-- The consumed wire prefix and untouched pipeline suffix partition the input
exactly; no byte can be lost, duplicated, or taken from the following message. -/
theorem decodeBodyReference_partition (cfg : Config) (bytes : ByteArray) (start : Nat)
    (initial : BodyState) (body : ByteArray) (trailers : Array (String × ByteArray)) (stop : Nat)
    (hs : start ≤ bytes.size) (hd : decodeBodyReference cfg bytes start initial = .done body trailers stop) :
    bytes.extract start stop ++ bytes.extract stop bytes.size = bytes.extract start bytes.size := by
  have bounds := decodeBodyReference_done_bounds cfg bytes start initial body trailers stop hs hd
  exact (ByteArray.extract_eq_extract_append_extract _ bounds.1 bounds.2).symm

/-- Every suspension contains a nonempty fixed remainder (or a chunk phase), so
restarting the decoder cannot introduce an epsilon completion. -/
def BodyLive (s : BodyState) : Prop :=
  match s.phase with
  | .fixed n => n ≠ 0
  | _ => True

theorem bodyByte_live (cfg : Config) (s next : BodyState) (b : UInt8)
    (h : bodyByte cfg s b = .more next) : BodyLive next := by
  cases hp : s.phase <;> simp [bodyByte, hp] at h
  all_goals repeat' split at h
  all_goals try dsimp at h
  all_goals first | contradiction | (cases h <;> simp_all [BodyLive] <;> omega)

theorem bodyInitial_live (s : BodyState) (count : Nat) (h : BodyLive s) :
    bodyInitial s count = ⟨.more s, count⟩ := by
  cases hp : s.phase <;> simp_all [bodyInitial, BodyLive]

theorem bodyAdvance_shift (cfg : Config) (s : BodyScan) (b : UInt8) (delta : Nat) :
    bodyAdvance cfg { s with count := s.count + delta } b =
      { bodyAdvance cfg s b with count := (bodyAdvance cfg s b).count + delta } := by
  cases s with
  | mk action count => cases action <;> simp [bodyAdvance, Nat.add_assoc, Nat.add_comm]

theorem bodyList_shift (cfg : Config) (s : BodyScan) (xs : List UInt8) (delta : Nat) :
    xs.foldl (bodyAdvance cfg) { s with count := s.count + delta } =
      { xs.foldl (bodyAdvance cfg) s with count := (xs.foldl (bodyAdvance cfg) s).count + delta } := by
  induction xs generalizing s with
  | nil => rfl
  | cons b xs ih => simpa [List.foldl_cons, bodyAdvance_shift] using ih (bodyAdvance cfg s b)

theorem bodyFeed_shift (cfg : Config) (s : BodyScan) (bytes : ByteArray) (delta : Nat) :
    bodyFeed cfg { s with count := s.count + delta } bytes =
      { bodyFeed cfg s bytes with count := (bodyFeed cfg s bytes).count + delta } := by
  simpa [bodyFeed_eq_fold, bodyFold, Array.foldl_toList] using bodyList_shift cfg s bytes.data.toList delta

theorem bodyList_more (cfg : Config) (s : BodyScan) (xs : List UInt8) (next : BodyState)
    (h : (xs.foldl (bodyAdvance cfg) s).action = .more next)
    (live : ∀ state, s.action = .more state → BodyLive state) :
    BodyLive next ∧ (xs.foldl (bodyAdvance cfg) s).count = s.count + xs.length := by
  induction xs generalizing s with
  | nil => exact ⟨live _ h, by simp⟩
  | cons b xs ih =>
    simp only [List.foldl_cons] at h ⊢
    cases hs : s.action with
    | more state =>
      have hl : ∀ next, (bodyAdvance cfg s b).action = .more next → BodyLive next := by
        intro next hn
        exact bodyByte_live cfg state next b (by simpa [bodyAdvance, hs] using hn)
      have rest := ih (bodyAdvance cfg s b) h hl
      simpa [bodyAdvance, hs, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using rest
    | done body trailers =>
      have ht : BodyTerminal s := by simp [BodyTerminal, hs]
      rw [bodyAdvance_terminal cfg s b ht, bodyList_terminal cfg s xs ht, hs] at h
      cases h
    | error status =>
      have ht : BodyTerminal s := by simp [BodyTerminal, hs]
      rw [bodyAdvance_terminal cfg s b ht, bodyList_terminal cfg s xs ht, hs] at h
      cases h

theorem bodyInitial_more_live (s state : BodyState) (count : Nat)
    (h : (bodyInitial s count).action = .more state) : BodyLive state := by
  cases hp : s.phase <;> simp_all [bodyInitial]
  all_goals repeat' split at h
  all_goals first | contradiction | (cases h <;> simp_all [BodyLive])

theorem bodyFeed_more_count (cfg : Config) (initial next : BodyState) (bytes : ByteArray)
    (h : (bodyFeed cfg (bodyInitial initial 0) bytes).action = .more next) :
    BodyLive next ∧ (bodyFeed cfg (bodyInitial initial 0) bytes).count = bytes.size := by
  have live := bodyInitial_more_live initial
  have hf : (bytes.data.toList.foldl (bodyAdvance cfg) (bodyInitial initial 0)).action = .more next := by
    simpa [bodyFeed_eq_fold, bodyFold, Array.foldl_toList] using h
  have result := bodyList_more cfg (bodyInitial initial 0) bytes.data.toList next hf (fun state h => live state 0 h)
  simpa [bodyFeed_eq_fold, bodyFold, Array.foldl_toList, bodyInitial] using result

/-- The offset adjustment needed when a completed body ends in a later receive
buffer. The decoder's cursor is relative to the buffer passed to that call. -/
def shiftBodyResult (delta : Nat) (result : BodyResult) : BodyResult :=
  match result with
  | .done body trailers stop => .done body trailers (stop + delta)
  | _ => result

theorem bodyScan_result_shift (s : BodyScan) (delta : Nat) :
    ({ s with count := s.count + delta } : BodyScan).result = shiftBodyResult delta s.result := by
  cases s with
  | mk action count => cases action <;> rfl

/-- Reference-decoder composition (transferred to the optimized public API in BodyFastProofs): suspending on
one receive buffer and resuming on the next preserves payload, trailers, errors,
and the exact first message boundary, for arbitrary bytes and starting states. -/
theorem decodeBodyReference_fragmentation (cfg : Config) (initial : BodyState) (a b : ByteArray) :
    decodeBodyReference cfg (a ++ b) 0 initial =
      match decodeBodyReference cfg a 0 initial with
      | .need next => shiftBodyResult a.size (decodeBodyReference cfg b 0 next)
      | terminal => terminal := by
  change (bodyFeed cfg (bodyInitial initial 0) (a ++ b)).result =
    match (bodyFeed cfg (bodyInitial initial 0) a).result with
    | .need next => shiftBodyResult a.size (bodyFeed cfg (bodyInitial next 0) b).result
    | terminal => terminal
  rw [bodyFeed_append]
  generalize he : bodyFeed cfg (bodyInitial initial 0) a = first
  cases first with
  | mk action count =>
    cases action with
    | more next =>
      have hn : (bodyFeed cfg (bodyInitial initial 0) a).action = .more next := by rw [he]
      have props := bodyFeed_more_count cfg initial next a hn
      rw [he] at props
      have hc : count = a.size := props.2
      have normalized := bodyInitial_live next 0 props.1
      simp only [BodyScan.result, normalized]
      subst count
      have shifted := bodyFeed_shift cfg (⟨.more next, 0⟩ : BodyScan) b a.size
      simp only [Nat.zero_add] at shifted
      rw [shifted]
      exact bodyScan_result_shift (bodyFeed cfg ⟨.more next, 0⟩ b) a.size
    | done body trailers =>
      rw [bodyFeed_terminal cfg _ b (by trivial)]
      rfl
    | error status =>
      rw [bodyFeed_terminal cfg _ b (by trivial)]
      rfl

/-- Exact fixed-body contents, for every payload, independent of its octets.
`foldl ByteArray.push` specifies byte-for-byte concatenation with the saved prefix. -/
theorem bodyList_fixed_exact (cfg : Config) (xs : List UInt8) (s : BodyState) (count : Nat) :
    xs.foldl (bodyAdvance cfg) (bodyInitial { s with phase := .fixed xs.length } count) =
      ⟨.done (xs.foldl ByteArray.push s.body) s.trailers, count + xs.length⟩ := by
  induction xs generalizing s count with
  | nil => simp [bodyInitial]
  | cons b xs ih =>
    cases xs with
    | nil => simp [bodyInitial, bodyAdvance, bodyByte, List.foldl_cons]
    | cons c xs =>
      have step : bodyAdvance cfg
          (bodyInitial { s with phase := .fixed (List.length (b :: c :: xs)) } count) b =
          bodyInitial { s with body := s.body.push b, phase := .fixed (List.length (c :: xs)) } (count + 1) := by
        simp [bodyInitial, bodyAdvance, bodyByte, Nat.add_assoc]
      rw [List.foldl_cons, step]
      simpa [List.foldl_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih { s with body := s.body.push b } (count + 1)

/-- Exact fixed-body decoding with an arbitrary pipelined suffix. -/
theorem bodyFeed_fixed_exact (cfg : Config) (payload suffix : ByteArray) (s : BodyState) :
    bodyFeed cfg (bodyInitial { s with phase := .fixed payload.size }) (payload ++ suffix) =
      ⟨.done (payload.data.foldl ByteArray.push s.body) s.trailers, payload.size⟩ := by
  rw [bodyFeed_append]
  have first : bodyFeed cfg (bodyInitial { s with phase := .fixed payload.size }) payload =
      ⟨.done (payload.data.foldl ByteArray.push s.body) s.trailers, payload.size⟩ := by
    simpa [bodyFeed_eq_fold, bodyFold, Array.foldl_toList] using bodyList_fixed_exact cfg payload.data.toList s 0
  rw [first, bodyFeed_terminal cfg _ suffix (by trivial)]

end FastHTTP.Protocol
