import FastHTTP.Batch
import Init.Data.ByteArray.Lemmas

namespace FastHTTP.AsyncStream.ReadyBatch

/-- Every buffered prefix is retained, with exactly the new bytes after it. -/
theorem append_data (buffer bytes : ByteArray) :
    (append buffer bytes).data.toList = buffer.data.toList ++ bytes.data.toList := by
  simp [append, ByteArray.data_append]

/-- No length loss, truncation, inserted separator, or character counting. -/
theorem append_size (buffer bytes : ByteArray) :
    (append buffer bytes).size = buffer.size + bytes.size := by
  simp [append]

theorem payload_prefix (chunks : List ByteArray) (initial : ByteArray) :
    payload chunks initial = initial ++ payload chunks := by
  induction chunks generalizing initial with
  | nil => simp [payload]
  | cons bytes rest ih =>
    simp only [payload, List.foldl_cons]
    change payload rest (append initial bytes) = initial ++ payload rest (append ByteArray.empty bytes)
    rw [ih, ih (append ByteArray.empty bytes)]
    simp [append, ByteArray.append_assoc]

/-- Repartitioning a completed stream into batches preserves its byte payload.
This is a pure data theorem; scheduler/lifetime behavior is tested separately. -/
theorem payload_partition (first rest : List ByteArray) :
    payload (first ++ rest) = payload first ++ payload rest := by
  simp only [payload, List.foldl_append]
  exact payload_prefix rest (payload first)

/-- Coalescing one adjacent pair cannot drop, duplicate or reorder bytes. -/
theorem coalesce_pair (a b : ByteArray) (rest : List ByteArray) :
    payload (append a b :: rest) = payload (a :: b :: rest) := by
  simp [payload, append]

end FastHTTP.AsyncStream.ReadyBatch
