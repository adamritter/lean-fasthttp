import FastHTTP.WireProofs
import FastHTTP.LexicalProofs

namespace FastHTTP.Protocol

def hexadecimalValue (xs : List UInt8) (n : Nat := 0) : Nat :=
  xs.foldl (fun n b => n * 16 + hexValue b) n

/-- Independent chunk-size numeral: nonempty RFC HEXDIG sequence with its
positional base-sixteen value; no reference to the executable parser. -/
def HexadecimalEncoding (xs : List UInt8) (n : Nat) : Prop :=
  xs ≠ [] ∧ (∀ b ∈ xs, HexOctet b) ∧ hexadecimalValue xs = n

theorem hexadecimalValue_mono (xs : List UInt8) (n : Nat) : n ≤ hexadecimalValue xs n := by
  induction xs generalizing n with
  | nil => simp [hexadecimalValue]
  | cons b xs ih =>
    have h := ih (n * 16 + hexValue b)
    simp only [hexadecimalValue, List.foldl_cons] at *
    omega

theorem hexadecimalStep_iff (limit n m : Nat) (b : UInt8) :
    hexadecimalStep limit n b = some m ↔
      HexOctet b ∧ m = n * 16 + hexValue b ∧ m ≤ limit := by
  simp only [hexadecimalStep, ← hexValue_iff]
  split <;> simp_all <;> omega

theorem hexadecimalFold_none (xs : List UInt8) (limit : Nat) :
    xs.foldl (fun acc b => acc.bind (fun k => hexadecimalStep limit k b)) none = none := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa using ih

/-- The bounded fold rejects exactly malformed digits or an excessive value. -/
theorem hexadecimalFold_iff (xs : List UInt8) (limit n m : Nat) (hn : n ≤ limit) :
    xs.foldl (fun acc b => acc.bind (fun k => hexadecimalStep limit k b)) (some n) = some m ↔
      (∀ b ∈ xs, HexOctet b) ∧ hexadecimalValue xs n = m ∧ m ≤ limit := by
  induction xs generalizing n with
  | nil => simp [hexadecimalValue]; omega
  | cons b xs ih =>
    simp only [List.foldl_cons, Option.bind_some, List.mem_cons, forall_eq_or_imp]
    cases hs : hexadecimalStep limit n b with
    | none =>
      rw [hexadecimalFold_none]
      constructor
      · intro h; contradiction
      · rintro ⟨⟨hb, ht⟩, hv, hm⟩
        have hv' : hexadecimalValue xs (n * 16 + hexValue b) = m := hv
        have hbound := hexadecimalValue_mono xs (n * 16 + hexValue b)
        have hstep : hexadecimalStep limit n b = some (n * 16 + hexValue b) :=
          (hexadecimalStep_iff _ _ _ _).mpr ⟨hb, rfl, by omega⟩
        simp [hs] at hstep
    | some next =>
      have hh := (hexadecimalStep_iff _ _ _ _).mp hs
      rw [ih next hh.2.2]
      simp only [hexadecimalValue, List.foldl_cons]
      simp_all [hexadecimalValue]

/-- Array traversal refines a fold over precisely the requested slice. -/
theorem hexadecimalLoop_eq_fold (bytes : ByteArray) (stop limit i n : Nat)
    (hi : i ≤ stop) (hs : stop ≤ bytes.size) :
    hexadecimalLoop bytes stop limit i n =
      ((bytes.data.toList.take stop).drop i).foldl
        (fun acc b => acc.bind (fun k => hexadecimalStep limit k b)) (some n) := by
  rw [hexadecimalLoop]
  split
  next h =>
    rw [List.drop_eq_getElem_cons (by simp; omega), List.foldl_cons]
    have hb : ((bytes.data.toList.take stop)[i]' (by simp; omega)) = bytes[i] := by
      simp only [List.getElem_take, Array.getElem_toList]
      exact ByteArray.getElem_eq_getElem_data.symm
    rw [hb]
    simp only [Option.bind_some]
    cases he : hexadecimalStep limit n bytes[i] with
    | none =>
      exact (hexadecimalFold_none _ limit).symm
    | some next => exact hexadecimalLoop_eq_fold bytes stop limit (i + 1) next (by omega) hs
  next h =>
    have he : i = stop := by omega
    subst i
    simp
termination_by stop - i

/-- Soundness and completeness of the bounded hexadecimal parser for arbitrary
limits, leading zeros and all octets, including malformed numerals. -/
theorem hexadecimal_iff (bytes : ByteArray) (start stop limit n : Nat) :
    hexadecimal bytes start stop limit = some n ↔
      start < stop ∧ stop ≤ bytes.size ∧
      HexadecimalEncoding (bytes.extract start stop).data.toList n ∧ n ≤ limit := by
  unfold hexadecimal
  split
  next h =>
    rw [hexadecimalLoop_eq_fold bytes stop limit start 0 (by omega) h.2, hexadecimalFold_iff _ limit 0 n (by omega)]
    have he : (bytes.extract start stop).data.toList = (bytes.data.toList.take stop).drop start := by
      simp [ByteArray.data_extract, Array.toList_extract, List.extract, List.take_drop, Nat.add_sub_cancel' (by omega : start ≤ stop)]
    have hn : (bytes.extract start stop).data.toList ≠ [] := by
      intro hn
      have := congrArg List.length hn
      simp at this
      omega
    simp_all [HexadecimalEncoding, and_assoc]
  next h =>
    constructor
    · intro he; contradiction
    · rintro ⟨hstart, hstop, _⟩
      exact False.elim (h ⟨hstart, hstop⟩)

/-- Every accepted production chunk-size line contains a nonempty, exact
hexadecimal numeral within the body limit and an accepted extension suffix. -/
theorem chunkSize_numeral (line : ByteArray) (limit n : Nat) (h : chunkSize line limit = .ok n) :
    ∃ stop, 0 < stop ∧ stop ≤ line.size ∧
      HexadecimalEncoding (line.extract 0 stop).data.toList n ∧ n ≤ limit ∧
      chunkExtensions line stop = .ok () := by
  unfold chunkSize at h
  dsimp only at h
  split at h
  · contradiction
  · cases hn : hexadecimal line 0 (spanEnd line line.size hexDigit 0) limit with
    | none => simp [hn] at h
    | some value =>
      simp only [hn] at h
      cases he : chunkExtensions line (spanEnd line line.size hexDigit 0) with
      | error status => simp [he] at h
      | ok valueUnit =>
        cases valueUnit
        simp only [he] at h
        cases h
        have props := (hexadecimal_iff _ _ _ _ _).mp hn
        exact ⟨_, props.1, props.2.1, props.2.2.1, props.2.2.2, he⟩

theorem chunkSize_bound (line : ByteArray) (limit n : Nat) (h : chunkSize line limit = .ok n) :
    n ≤ limit := by
  obtain ⟨_, _, _, _, bound, _⟩ := chunkSize_numeral line limit n h
  exact bound

end FastHTTP.Protocol
