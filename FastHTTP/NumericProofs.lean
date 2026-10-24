import FastHTTP.Numeric
import Std.Tactic

namespace FastHTTP.Protocol

/-- RFC 9110 DIGIT, expressed as mathematical octet intervals. -/
def DecimalOctet (b : UInt8) : Prop := 48 ≤ b.toNat ∧ b.toNat ≤ 57

def decimalValue (xs : List UInt8) (n : Nat := 0) : Nat :=
  xs.foldl (fun n b => n * 10 + (b.toNat - 48)) n

/-- Independent Content-Length specification: nonempty DIGIT sequence and its
positional base-ten value; no reference to the executable parser. -/
def DecimalEncoding (xs : List UInt8) (n : Nat) : Prop :=
  xs ≠ [] ∧ (∀ b ∈ xs, DecimalOctet b) ∧ decimalValue xs = n

theorem decimalValue_mono (xs : List UInt8) (n : Nat) : n ≤ decimalValue xs n := by
  induction xs generalizing n with
  | nil => simp [decimalValue]
  | cons b xs ih =>
    have h := ih (n * 10 + (b.toNat - 48))
    simp only [decimalValue, List.foldl_cons] at *
    omega

theorem decimalStep_iff (limit n m : Nat) (b : UInt8) :
    decimalStep limit n b = some m ↔
      DecimalOctet b ∧ m = n * 10 + (b.toNat - 48) ∧ m ≤ limit := by
  simp only [decimalStep, DecimalOctet]
  split <;> simp_all <;> omega

theorem decimalFold_none (xs : List UInt8) (limit : Nat) :
    xs.foldl (fun acc b => acc.bind (fun k => decimalStep limit k b)) none = none := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa using ih

/-- The bounded fold rejects exactly malformed digits or an excessive value. -/
theorem decimalFold_iff (xs : List UInt8) (limit n m : Nat) (hn : n ≤ limit) :
    xs.foldl (fun acc b => acc.bind (fun k => decimalStep limit k b)) (some n) = some m ↔
      (∀ b ∈ xs, DecimalOctet b) ∧ decimalValue xs n = m ∧ m ≤ limit := by
  induction xs generalizing n with
  | nil => simp [decimalValue]; omega
  | cons b xs ih =>
    simp only [List.foldl_cons, Option.bind_some, List.mem_cons, forall_eq_or_imp]
    cases hs : decimalStep limit n b with
    | none =>
      rw [decimalFold_none]
      constructor
      · intro h; contradiction
      · rintro ⟨⟨hb, ht⟩, hv, hm⟩
        have hv' : decimalValue xs (n * 10 + (b.toNat - 48)) = m := hv
        have hbound := decimalValue_mono xs (n * 10 + (b.toNat - 48))
        have hstep : decimalStep limit n b = some (n * 10 + (b.toNat - 48)) :=
          (decimalStep_iff _ _ _ _).mpr ⟨hb, rfl, by omega⟩
        simp [hs] at hstep
    | some next =>
      have hh := (decimalStep_iff _ _ _ _).mp hs
      rw [ih next hh.2.2]
      simp only [decimalValue, List.foldl_cons]
      simp_all [decimalValue]

/-- Array traversal refines a fold over precisely the requested slice. -/
theorem decimalLoop_eq_fold (bytes : ByteArray) (stop limit i n : Nat)
    (hi : i ≤ stop) (hs : stop ≤ bytes.size) :
    decimalLoop bytes stop limit i n =
      ((bytes.data.toList.take stop).drop i).foldl
        (fun acc b => acc.bind (fun k => decimalStep limit k b)) (some n) := by
  rw [decimalLoop]
  split
  next h =>
    rw [List.drop_eq_getElem_cons (by simp; omega), List.foldl_cons]
    have hb : ((bytes.data.toList.take stop)[i]' (by simp; omega)) = bytes[i] := by
      simp only [List.getElem_take, Array.getElem_toList]
      exact ByteArray.getElem_eq_getElem_data.symm
    rw [hb]
    simp only [Option.bind_some]
    cases he : decimalStep limit n bytes[i] with
    | none =>
      exact (decimalFold_none _ limit).symm
    | some next => exact decimalLoop_eq_fold bytes stop limit (i + 1) next (by omega) hs
  next h =>
    have he : i = stop := by omega
    subst i
    simp
termination_by stop - i

/-- Soundness and completeness of the production Content-Length parser. This
includes arbitrary limits, leading zeros and all possible non-digit octets. -/
theorem decimal_iff (bytes : ByteArray) (start stop limit n : Nat) :
    decimal bytes start stop limit = some n ↔
      start < stop ∧ stop ≤ bytes.size ∧
      DecimalEncoding (bytes.extract start stop).data.toList n ∧ n ≤ limit := by
  unfold decimal
  split
  next h =>
    rw [decimalLoop_eq_fold bytes stop limit start 0 (by omega) h.2, decimalFold_iff _ limit 0 n (by omega)]
    have he : (bytes.extract start stop).data.toList = (bytes.data.toList.take stop).drop start := by
      simp [ByteArray.data_extract, Array.toList_extract, List.extract, List.take_drop, Nat.add_sub_cancel' (by omega : start ≤ stop)]
    have hn : (bytes.extract start stop).data.toList ≠ [] := by
      intro hn
      have := congrArg List.length hn
      simp at this
      omega
    simp_all [DecimalEncoding, and_assoc]
  next h =>
    constructor
    · intro he; contradiction
    · rintro ⟨hstart, hstop, _⟩
      exact False.elim (h ⟨hstart, hstop⟩)

end FastHTTP.Protocol
