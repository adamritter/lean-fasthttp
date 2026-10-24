import FastHTTP.Response
import Init.Data.ByteArray.Lemmas
import Init.Data.Array.Lemmas
import Std.Tactic

/-! These theorems concern the executable primitives imported above, not a
second parser. They do NOT establish full RFC conformance or transport liveness.
No sorry, custom axioms, unsafe definitions, or native_decide are used here. -/
namespace FastHTTP.Protocol

/-- TCP fragmentation does not change delimiter detection, including its limit
and first-delimiter offset. This is the scanner called by `feed`. -/
theorem scanFeed_append (limit : Nat) (s : ScanState) (a b : ByteArray) :
    scanFeed limit s (a ++ b) = scanFeed limit (scanFeed limit s a) b := by
  simp only [scanFeed, ByteArray.data_append, Array.foldl_append]

/-- Arbitrarily many receive buffers have the same scanner result as concatenation. -/
theorem scanFeed_fragments (limit : Nat) (s : ScanState) (chunks : List ByteArray) :
    chunks.foldl (scanFeed limit) s =
      scanFeed limit s (chunks.foldl (· ++ ·) ByteArray.empty) := by
  have aux : ∀ (xs : List ByteArray) (acc : ByteArray),
      xs.foldl (scanFeed limit) (scanFeed limit s acc) =
        scanFeed limit s (xs.foldl (· ++ ·) acc) := by
    intro xs
    induction xs with
    | nil => intro acc; rfl
    | cons x xs ih =>
      intro acc
      simp only [List.foldl_cons, ← scanFeed_append]
      exact ih (acc ++ x)
  simpa [scanFeed] using aux chunks ByteArray.empty

/-- A detected delimiter cannot be replaced by a later one. -/
theorem scanByte_stopped (limit : Nat) (s : ScanState) (b : UInt8) (n : Nat)
    (h : s.stop = some n) : scanByte limit s b = s := by
  simp [scanByte, h]

/-- Bytes after the header boundary do not affect a completed scanner. -/
theorem scanFeed_stopped (limit : Nat) (s : ScanState) (bytes : ByteArray) (n : Nat)
    (h : s.stop = some n) : scanFeed limit s bytes = s := by
  unfold scanFeed
  rw [← Array.foldl_toList]
  have aux : ∀ xs : List UInt8, xs.foldl (scanByte limit) s = s := by
    intro xs
    induction xs with
    | nil => rfl
    | cons x xs ih => simpa [List.foldl_cons, scanByte_stopped limit s x n h] using ih
  exact aux _

theorem conflicting_framing_rejected (n : Nat) :
    chooseFraming (some n) true = .error 400 := rfl

theorem fixed_framing_exact (n : Nat) :
    chooseFraming (some n) false = .ok (.fixed n) := rfl

/-- No overconsumption of either the promised body or the available input. -/
theorem takeCount_bounds (remaining available : Nat) :
    takeCount remaining available ≤ remaining ∧ takeCount remaining available ≤ available := by
  unfold takeCount
  omega

theorem takeCount_conservation (remaining available : Nat) :
    takeCount remaining available + (remaining - takeCount remaining available) = remaining := by
  unfold takeCount
  omega

/-- Fixed-length consumption is independent of input fragmentation. -/
theorem takeCount_fragmentation (n a b : Nat) :
    takeCount n (a + b) = takeCount n a + takeCount (n - takeCount n a) b := by
  unfold takeCount
  omega

theorem takeBody_bounds (bytes : ByteArray) (start remaining : Nat) (h : start ≤ bytes.size) :
    start ≤ (takeBody bytes start remaining).2 ∧
    (takeBody bytes start remaining).2 ≤ bytes.size := by
  simp only [takeBody, takeCount]
  omega

theorem takeBody_size (bytes : ByteArray) (start remaining : Nat) (h : start ≤ bytes.size) :
    (takeBody bytes start remaining).1.size = takeCount remaining (bytes.size - start) := by
  simp only [takeBody, ByteArray.size_extract, takeCount]
  omega

/-- Exact byte preservation: consumed body followed by untouched suffix equals
all input from the cursor. The suffix may contain the next pipelined request. -/
theorem takeBody_partition (bytes : ByteArray) (start remaining : Nat) (h : start ≤ bytes.size) :
    (takeBody bytes start remaining).1 ++
      bytes.extract (takeBody bytes start remaining).2 bytes.size =
        bytes.extract start bytes.size := by
  have bounds := takeBody_bounds bytes start remaining h
  exact (ByteArray.extract_eq_extract_append_extract _ bounds.1 bounds.2).symm

/-- Once the fixed-length body is present, its cursor is exactly its declared end. -/
theorem takeBody_complete (bytes : ByteArray) (start remaining : Nat)
    (h : start + remaining ≤ bytes.size) :
    (takeBody bytes start remaining).2 = start + remaining := by
  simp only [takeBody, takeCount]
  omega

/-- Byte-level fixed-body fragmentation, not just equality of consumed counts. -/
theorem takeBody_bytes_fragmentation (a b : ByteArray) (n : Nat) :
    (takeBody (a ++ b) 0 n).1 =
      (takeBody a 0 n).1 ++ (takeBody b 0 (n - a.size)).1 := by
  simp only [takeBody, takeCount, Nat.sub_zero, Nat.zero_add]
  have trim (bytes : ByteArray) (k : Nat) : bytes.extract 0 (min k bytes.size) = bytes.extract 0 k := by
    apply ByteArray.ext_getElem
    · simp [ByteArray.size_extract, Nat.min_assoc]
    · intro i hi hi'
      simp only [ByteArray.getElem_extract]
  rw [trim, trim, trim, ByteArray.extract_append]
  simp

theorem head_has_no_body (status : Nat) (body : ByteArray) :
    wireBody status true body = ByteArray.empty := by simp [wireBody]

theorem no_content_has_no_body (isHead : Bool) (body : ByteArray) :
    wireBody 204 isHead body = ByteArray.empty := by simp [wireBody]

theorem not_modified_has_no_body (isHead : Bool) (body : ByteArray) :
    wireBody 304 isHead body = ByteArray.empty := by simp [wireBody]

theorem no_content_omits_length (body : ByteArray) : responseLength 204 body = none := rfl

/-- For ordinary non-HEAD responses the advertised size equals the emitted body. -/
theorem response_length_exact (status : Nat) (body : ByteArray)
    (h204 : status ≠ 204) (h205 : status ≠ 205) (h304 : status ≠ 304) :
    responseLength status body = some (wireBody status false body).size := by
  simp [responseLength, wireBody, h204, h205, h304]

end FastHTTP.Protocol
