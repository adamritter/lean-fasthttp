import FastHTTP.HexProofs
import FastHTTP.BodyFastProofs

namespace FastHTTP.Protocol

/-- The current payload plus any promised fixed/chunk data fits in the budget. -/
def BodyBudget (cfg : Config) (s : BodyState) : Prop :=
  s.body.size ≤ cfg.maxBodyBytes ∧
    match s.phase with
    | .fixed n | .data n => s.body.size + n ≤ cfg.maxBodyBytes
    | _ => True

def BodyActionBudget (cfg : Config) : BodyAction → Prop
  | .more s => BodyBudget cfg s
  | .done body _ => body.size ≤ cfg.maxBodyBytes
  | .error _ => True

/-- Every executed octet preserves the body budget, including fresh chunk-size
lines, binary data, trailers, invalid syntax and all early-return branches. -/
theorem bodyByte_budget (cfg : Config) (s : BodyState) (b : UInt8) (hs : BodyBudget cfg s) :
    BodyActionBudget cfg (bodyByte cfg s b) := by
  cases hp : s.phase <;> simp [bodyByte, hp]
  all_goals repeat' split
  all_goals try (have hsize := chunkSize_bound _ _ _ (by assumption))
  all_goals simp_all [BodyActionBudget, BodyBudget] <;> omega

theorem bodyInitial_budget (cfg : Config) (state : BodyState) (start : Nat) (hs : BodyBudget cfg state) :
    BodyActionBudget cfg (bodyInitial state start).action := by
  cases hp : state.phase with
  | fixed n => cases n <;> simp_all [bodyInitial, BodyActionBudget, BodyBudget]
  | _ => simpa [bodyInitial, hp, BodyActionBudget] using hs

theorem bodyAdvance_budget (cfg : Config) (state : BodyScan) (b : UInt8)
    (hs : BodyActionBudget cfg state.action) :
    BodyActionBudget cfg (bodyAdvance cfg state b).action := by
  cases state with
  | mk action count =>
    cases action with
    | more next => exact bodyByte_budget cfg next b hs
    | done body trailers => exact hs
    | error status => trivial

theorem bodyList_budget (cfg : Config) (state : BodyScan) (bytes : List UInt8)
    (hs : BodyActionBudget cfg state.action) :
    BodyActionBudget cfg (bytes.foldl (bodyAdvance cfg) state).action := by
  induction bytes generalizing state with
  | nil => exact hs
  | cons b bytes ih => exact ih _ (bodyAdvance_budget cfg state b hs)

def BodyResultBudget (cfg : Config) : BodyResult → Prop
  | .need state => BodyBudget cfg state
  | .done body _ _ => body.size ≤ cfg.maxBodyBytes
  | .error _ => True

/-- The actual optimized decoder cannot exceed its configured body limit when
started in a state with a valid budget. Every suspension preserves that budget. -/
theorem decodeBody_budget (cfg : Config) (bytes : ByteArray) (start : Nat) (state : BodyState)
    (hs : BodyBudget cfg state) : BodyResultBudget cfg (decodeBody cfg bytes start state) := by
  rw [decodeBody_eq_reference]
  unfold decodeBodyReference
  rw [bodyLoop_eq_fold]
  have bound := bodyList_budget cfg (bodyInitial state start) (bytes.data.toList.drop start)
    (bodyInitial_budget cfg state start hs)
  generalize he : (bytes.data.toList.drop start).foldl (bodyAdvance cfg) (bodyInitial state start) = result at *
  cases result with
  | mk action count => cases action <;> exact bound

end FastHTTP.Protocol
