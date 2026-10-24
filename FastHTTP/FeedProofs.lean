import FastHTTP.BodyFastProofs

namespace FastHTTP.Protocol

/-- Appending transport bytes to an already observed action. A completed request
retains those bytes as pipeline input; an Expect action retains them until the
interim response is sent. No request fields are erased from this comparison. -/
def appendStep (cfg : Config) (step : Step) (input : ByteArray) : Step :=
  match step with
  | .need state => feed cfg state input
  | .«continue» (.body request decoder pending start) =>
    .«continue» (.body request decoder (pending ++ input) start)
  | .«continue» state => .«continue» state
  | .request request rest => .request request (rest ++ input)
  | .reject status => .reject status

theorem append_unless_empty (pending input : ByteArray) :
    (if pending.isEmpty then input else pending ++ input) = pending ++ input := by
  by_cases h : pending.isEmpty = true
  · have he : pending = .empty := by
      apply ByteArray.ext
      simpa [ByteArray.isEmpty] using Array.isEmpty_iff.mp h
    simp [he]
  · simp [h]

theorem extract_prefix_append (a b : ByteArray) (stop : Nat) (hs : stop ≤ a.size) :
    (a ++ b).extract 0 stop = a.extract 0 stop := by
  rw [ByteArray.extract_append]
  simp [Nat.sub_eq_zero_of_le hs]

theorem extract_suffix_append (a b : ByteArray) (start : Nat) (hs : start ≤ a.size) :
    (a ++ b).extract start (a ++ b).size = a.extract start a.size ++ b := by
  rw [ByteArray.extract_append]
  simp only [ByteArray.size_append, Nat.add_sub_cancel_left, Nat.sub_eq_zero_of_le hs,
    ByteArray.extract_zero_size]
  congr 1
  apply ByteArray.ext
  simp only [ByteArray.data_extract]
  apply Array.extract_eq_extract_right.mpr
  simp only [← ByteArray.size_data]
  omega

theorem decodeBody_extract (cfg : Config) (bytes : ByteArray) (start : Nat) (initial : BodyState)
    (_hs : start ≤ bytes.size) :
    decodeBody cfg bytes start initial =
      shiftBodyResult start (decodeBody cfg (bytes.extract start bytes.size) 0 initial) := by
  simp only [decodeBody_eq_reference, decodeBodyReference, bodyLoop_eq_fold]
  have he : (bytes.extract start bytes.size).data.toList = bytes.data.toList.drop start := by
    simp only [ByteArray.data_extract, Array.toList_extract]
    apply List.take_of_length_le
    simp
  rw [he]
  simp only [List.drop_zero]
  have hi : bodyInitial initial start =
      { bodyInitial initial 0 with count := (bodyInitial initial 0).count + start } := by
    simp [bodyInitial]
  rw [hi, bodyList_shift, bodyScan_result_shift]

theorem bodyStep_extract (cfg : Config) (request : Request) (decoder : BodyState)
    (bytes : ByteArray) (start : Nat) (hs : start ≤ bytes.size) :
    bodyStep cfg request decoder bytes start =
      bodyStep cfg request decoder (bytes.extract start bytes.size) 0 := by
  unfold bodyStep
  rw [decodeBody_extract cfg bytes start decoder hs]
  cases he : decodeBody cfg (bytes.extract start bytes.size) 0 decoder with
  | need next => rfl
  | error status => rfl
  | done body trailers stop =>
    simp only [shiftBodyResult, ByteArray.extract_extract, ByteArray.size_extract, Nat.min_self]
    have hb := decodeBody_done_bounds cfg (bytes.extract start bytes.size) 0 decoder body trailers stop (by omega) he
    congr 1
    congr 1 <;> omega

/-- Body completion lifts to the public request action, including every request
metadata field, raw trailers, rejection status and the untouched pipeline bytes. -/
theorem bodyStep_append (cfg : Config) (request : Request) (decoder : BodyState) (a b : ByteArray) :
    bodyStep cfg request decoder (a ++ b) 0 = appendStep cfg (bodyStep cfg request decoder a 0) b := by
  unfold bodyStep
  rw [decodeBody_fragmentation]
  cases ha : decodeBody cfg a 0 decoder with
  | error status => rfl
  | need next =>
    simp only [appendStep, feed, ByteArray.empty_append, ite_self]
    unfold bodyStep
    cases hb : decodeBody cfg b 0 next with
    | need state => rfl
    | error status => rfl
    | done body trailers stop =>
      simp only [shiftBodyResult]
      congr 1
      have he : stop + a.size = a.size + stop := by omega
      rw [he, ByteArray.size_append, ByteArray.extract_append_size_add]
  | done body trailers stop =>
    simp only [appendStep]
    congr 1
    exact extract_suffix_append a b stop (decodeBody_done_bounds cfg a 0 decoder body trailers stop (by omega) ha).2

theorem bodyStep_append_start (cfg : Config) (request : Request) (decoder : BodyState)
    (a b : ByteArray) (start : Nat) (hs : start ≤ a.size) :
    bodyStep cfg request decoder (a ++ b) start = appendStep cfg (bodyStep cfg request decoder a start) b := by
  rw [bodyStep_extract cfg request decoder (a ++ b) start (by simp; omega),
    extract_suffix_append a b start hs, bodyStep_append, bodyStep_extract cfg request decoder a start hs]

/-- A stopped scan cursor never points beyond the consumed prefix. -/
def ScanBound (s : ScanState) : Prop := ∀ stop, s.stop = some stop → stop ≤ s.count

theorem scanByte_bounds (limit : Nat) (s : ScanState) (b : UInt8) (hs : ScanBound s) :
    (scanByte limit s b).count ≤ s.count + 1 ∧ ScanBound (scanByte limit s b) := by
  unfold scanByte
  split
  · exact ⟨by omega, hs⟩
  · split
    · exact ⟨by simp, hs⟩
    · constructor
      · simp
      · intro stop hstop
        simp only at hstop ⊢
        split at hstop <;> simp_all

theorem scanList_bounds (limit : Nat) (s : ScanState) (xs : List UInt8) (hs : ScanBound s) :
    (xs.foldl (scanByte limit) s).count ≤ s.count + xs.length ∧
      ScanBound (xs.foldl (scanByte limit) s) := by
  induction xs generalizing s with
  | nil => exact ⟨by simp, hs⟩
  | cons b xs ih =>
    have step := scanByte_bounds limit s b hs
    have rest := ih (scanByte limit s b) step.2
    exact ⟨by simp only [List.foldl_cons, List.length_cons]; omega, rest.2⟩

theorem scanFeedFast_bounds (limit : Nat) (s : ScanState) (bytes : ByteArray) (hs : ScanBound s) :
    (scanFeedFast limit s bytes).count ≤ s.count + bytes.size ∧
      ScanBound (scanFeedFast limit s bytes) := by
  simp only [scanFeedFast_eq_scanFeed, scanFeed]
  rw [← Array.foldl_toList]
  simpa using scanList_bounds limit s bytes.data.toList hs

/-- Completing a header commits its exact prefix and metadata. Later bytes may
only extend the body or the pipeline, including when Expect suspends processing. -/
theorem headStep_append (cfg : Config) (a b : ByteArray) (scanner : ScanState)
    (hc : scanner.count ≤ a.size) (hs : ScanBound scanner)
    (ht : (scanner.stop.isSome || scanner.invalid) = true) :
    headStep cfg (a ++ b) scanner = appendStep cfg (headStep cfg a scanner) b := by
  by_cases he : scanner.invalid = true
  · simp only [headStep, he, ite_true, appendStep, extract_prefix_append a b scanner.count hc]
  · have hn : scanner.invalid = false := by cases hi : scanner.invalid <;> simp_all
    cases hstop : scanner.stop with
    | none => simp [hstop, hn] at ht
    | some stop =>
      have bound : stop ≤ a.size := Nat.le_trans (hs stop hstop) hc
      simp only [headStep, hn, Bool.false_eq_true, ite_false, hstop,
        extract_prefix_append a b stop bound]
      cases hp : parseHead cfg (a.extract 0 stop) stop with
      | error status => rfl
      | ok head =>
        by_cases hf : head.framing == Framing.fixed 0
        · simp only [hf, ite_true, appendStep, extract_suffix_append a b stop bound]
        · simp only [hf, Bool.false_eq_true, ite_false]
          cases hx : head.expectContinue with
          | true => rfl
          | false =>
            simp only [Bool.false_eq_true, ite_false]
            exact bodyStep_append_start cfg head.request _ a b stop bound

/-- Public head-stage fragmentation, including incomplete headers, limits,
parse failures, fixed/chunked bodies, metadata and Expect/100-continue. -/
theorem feed_head_fragmentation (cfg : Config) (pending : ByteArray) (scanner : ScanState)
    (a b : ByteArray) (hc : scanner.count ≤ pending.size) (hs : ScanBound scanner) :
    feed cfg (.head pending scanner) (a ++ b) =
      appendStep cfg (feed cfg (.head pending scanner) a) b := by
  simp only [feed, append_unless_empty, scanFeedFast_append]
  rw [← ByteArray.append_assoc]
  let first := scanFeedFast cfg.maxHeaderBytes scanner a
  have bounds := scanFeedFast_bounds cfg.maxHeaderBytes scanner a hs
  have hb : first.count ≤ (pending ++ a).size := by
    simp only [ByteArray.size_append]
    dsimp [first]; omega
  by_cases ht : (first.stop.isSome || first.invalid) = true
  · have absorb : scanFeedFast cfg.maxHeaderBytes first b = first := by
      rw [scanFeedFast_eq_scanFeed]
      unfold scanFeed
      rw [← Array.foldl_toList]
      exact scanList_absorbed cfg.maxHeaderBytes first b.data.toList ht
    change headStep cfg ((pending ++ a) ++ b) (scanFeedFast cfg.maxHeaderBytes first b) = _
    rw [absorb]
    exact headStep_append cfg (pending ++ a) b first hb bounds.2 ht
  · have hn : first.invalid = false ∧ first.stop = none := by
      cases hi : first.invalid <;> cases ho : first.stop <;> simp_all
    have need : headStep cfg (pending ++ a) first = .need (.head (pending ++ a) first) := by
      simp [headStep, hn.1, hn.2]
    change headStep cfg ((pending ++ a) ++ b) (scanFeedFast cfg.maxHeaderBytes first b) =
      appendStep cfg (headStep cfg (pending ++ a) first) b
    rw [need]
    simp only [appendStep, feed, append_unless_empty]

theorem feed_body_fragmentation (cfg : Config) (request : Request) (decoder : BodyState)
    (pending a b : ByteArray) (start : Nat) (hs : start ≤ pending.size) :
    feed cfg (.body request decoder pending start) (a ++ b) =
      appendStep cfg (feed cfg (.body request decoder pending start) a) b := by
  simp only [feed, append_unless_empty]
  rw [← ByteArray.append_assoc]
  exact bodyStep_append_start cfg request decoder (pending ++ a) b start (by simp; omega)

def StateBound : State → Prop
  | .head pending scanner => scanner.count ≤ pending.size ∧ ScanBound scanner
  | .body _ _ pending start => start ≤ pending.size

/-- Full feed-interface composition. Equality includes the entire Request,
including raw bytes and all metadata: there is no semantic projection/filter. -/
theorem feed_fragmentation (cfg : Config) (state : State) (a b : ByteArray) (hs : StateBound state) :
    feed cfg state (a ++ b) = appendStep cfg (feed cfg state a) b := by
  cases state with
  | head pending scanner => exact feed_head_fragmentation cfg pending scanner a b hs.1 hs.2
  | body request decoder pending start => exact feed_body_fragmentation cfg request decoder pending a b start hs

theorem initial_state_bound : StateBound (.head) := by
  constructor
  · simp
  · intro stop hs; simp at hs

/-- The application-facing initial parser has identical complete results for
any two receive buffers or their concatenation. -/
theorem feed_initial_fragmentation (cfg : Config) (a b : ByteArray) :
    feed cfg (.head) (a ++ b) = appendStep cfg (feed cfg (.head) a) b :=
  feed_fragmentation cfg (.head) a b initial_state_bound

/-- The binary composition law covers every finite list of TCP fragments,
including empty fragments. Pending Expect actions buffer later bytes explicitly. -/
theorem feed_fragments (cfg : Config) (state : State) (chunks : List ByteArray)
    (prior : ByteArray) (hs : StateBound state) :
    chunks.foldl (appendStep cfg) (feed cfg state prior) =
      feed cfg state (chunks.foldl (· ++ ·) prior) := by
  induction chunks generalizing prior with
  | nil => rfl
  | cons a chunks ih =>
    simp only [List.foldl_cons]
    rw [← feed_fragmentation cfg state prior a hs]
    exact ih (prior ++ a)

def StepBound : Step → Prop
  | .need state | .«continue» state => StateBound state
  | _ => True

theorem bodyStep_bound (cfg : Config) (request : Request) (decoder : BodyState)
    (bytes : ByteArray) (start : Nat) : StepBound (bodyStep cfg request decoder bytes start) := by
  unfold bodyStep
  cases decodeBody cfg bytes start decoder <;> simp [StepBound, StateBound]

theorem headStep_bound (cfg : Config) (bytes : ByteArray) (scanner : ScanState)
    (hc : scanner.count ≤ bytes.size) (hs : ScanBound scanner) :
    StepBound (headStep cfg bytes scanner) := by
  unfold headStep
  split
  · trivial
  · cases he : scanner.stop with
    | none => exact ⟨hc, hs⟩
    | some stop =>
      simp only []
      cases parseHead cfg (bytes.extract 0 stop) stop with
      | error status => trivial
      | ok head =>
        simp only []
        split
        · trivial
        · split
          · exact Nat.le_trans (hs stop he) hc
          · exact bodyStep_bound cfg head.request _ bytes stop

/-- Every suspended continuation emitted by the real parser satisfies the
precondition needed to apply the composition theorem again. -/
theorem feed_bound (cfg : Config) (state : State) (input : ByteArray) (hs : StateBound state) :
    StepBound (feed cfg state input) := by
  cases state with
  | body request decoder pending start => exact bodyStep_bound cfg request decoder _ start
  | head pending scanner =>
    simp only [feed, append_unless_empty]
    have hb := scanFeedFast_bounds cfg.maxHeaderBytes scanner input hs.2
    exact headStep_bound cfg (pending ++ input) _ (by simp only [ByteArray.size_append]; have := hs.1; omega) hb.2

/-- A body continuation can never emit a second 100-continue action. -/
theorem feed_body_no_continue (cfg : Config) (request : Request) (decoder : BodyState)
    (pending input : ByteArray) (start : Nat) (next : State) :
    feed cfg (.body request decoder pending start) input ≠ .«continue» next := by
  simp only [feed, bodyStep]
  cases decodeBody cfg (if pending.isEmpty then input else pending ++ input) start decoder <;> simp

end FastHTTP.Protocol
