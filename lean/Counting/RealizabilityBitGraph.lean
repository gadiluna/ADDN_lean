import Counting.RealizabilityActiveReachability

namespace Counting.RealizabilityVerifier.BitGraph

/-- Flat Boolean storage. Missing positions have the declared false default. -/
def bitAt (bits : List Bool) (index : Nat) : Bool := bits[index]?.getD false

def edge (size : Nat) (bits : List Bool) (source target : Fin size) : Bool :=
  bitAt bits (source.val*size+target.val)

def initial (size : Nat) (source : Fin size) : List Bool :=
  (List.finRange size).map (fun target => target == source)

def reachPass (size : Nat) (arcs seen : List Bool) : List Bool :=
  (List.finRange size).map (fun target => bitAt seen target.val ||
    (List.finRange size).any (fun source => bitAt seen source.val && edge size arcs source target))

def iterate (size : Nat) (arcs : List Bool) (source : Fin size) : Nat → List Bool
  | 0 => initial size source
  | steps+1 => reachPass size arcs (iterate size arcs source steps)

def check (size : Nat) (arcs active : List Bool) : Bool :=
  (List.finRange size).all (fun source => !bitAt active source.val ||
    (List.finRange size).all (fun target => !bitAt active target.val ||
      bitAt (iterate size arcs source size) target.val))

theorem initial_at (size : Nat) (source target : Fin size) :
    bitAt (initial size source) target.val = (target == source) := by
  simp only [bitAt,initial,←List.ofFn_eq_map,List.getElem?_ofFn,dif_pos target.isLt,Option.getD_some]

theorem reachPass_at (size : Nat) (arcs seen : List Bool) (target : Fin size) :
    bitAt (reachPass size arcs seen) target.val =
      (bitAt seen target.val || (List.finRange size).any
        (fun source => bitAt seen source.val && edge size arcs source target)) := by
  simp only [bitAt,reachPass,←List.ofFn_eq_map,List.getElem?_ofFn,dif_pos target.isLt,Option.getD_some]

@[simp] theorem reachPass_length (size : Nat) (arcs seen : List Bool) :
    (reachPass size arcs seen).length=size := by simp [reachPass]

@[simp] theorem iterate_length (size : Nat) (arcs : List Bool) (source : Fin size) (steps : Nat) :
    (iterate size arcs source steps).length=size := by
  cases steps <;> simp [iterate,initial]

/-- Every synchronous bit-vector pass adds exactly one reachability step. -/
theorem iterate_mem (size : Nat) (arcs : List Bool) (source : Fin size) (steps : Nat) :
    ∀ target : Fin size,bitAt (iterate size arcs source steps) target.val=true ↔
      target ∈ reachable (edge size arcs) source steps := by
  induction steps with
  | zero => intro target; simp only [iterate,initial_at,beq_iff_eq,reachable,Finset.mem_singleton]
  | succ steps ih =>
    intro target
    simp only [iterate,reachPass_at,Bool.or_eq_true,List.any_eq_true,Bool.and_eq_true,
      List.mem_finRange,true_and,ih,reachable,mem_reachStep]

/-- The checker loops over explicit slots and exactly `size` passes. -/
theorem check_eq (size : Nat) (arcs active : List Bool) :
    check size arcs active = activeConnectedCheck (fun i : Fin size => bitAt active i.val) (edge size arcs) := by
  apply Bool.eq_iff_iff.mpr
  simp only [check,List.all_eq_true,List.mem_finRange,true_implies,Bool.or_eq_true,
    Bool.not_eq_true',iterate_mem,activeConnectedCheck,decide_eq_true_eq,Fintype.card_fin]
  constructor
  · intro accepted source sourceActive target targetActive
    have fromSource := accepted source
    simp only [sourceActive,Bool.true_eq_false,false_or] at fromSource
    have toTarget := fromSource target
    simpa only [targetActive,Bool.true_eq_false,false_or] using toTarget
  · intro accepted source
    cases sourceActive : bitAt active source.val
    · exact Or.inl rfl
    · right
      intro target
      cases targetActive : bitAt active target.val
      · exact Or.inl rfl
      · exact Or.inr (accepted source sourceActive target targetActive)

end Counting.RealizabilityVerifier.BitGraph
