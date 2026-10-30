import Counting.StackRealizabilityPointValues
import Counting.StackRealizabilityMassSpec
import Counting.RealizabilityCompactFields

namespace Counting.StackMachine.RealizabilityCheck
open RealizabilityVerifier RealizabilityVerifier.CompactGraph
set_option backward.isDefEq.respectTransparency false

theorem leavingRangeValues_ofFn (nodes : List Executable.Node) (values : List Nat)
    (target start count : Nat) :
    leavingRangeValues nodes values target start count=List.ofFn (fun j : Fin count=>
      decide (0<values[start+j.val]?.getD 0-childRangeSum nodes target (start+j.val) 0 values)) := by
  induction count generalizing start with
  | zero=>rfl
  | succ count ih=>
    rw [leavingRangeValues,List.ofFn_succ,ih]
    simp only [Fin.val_zero,Nat.add_zero,Fin.val_succ]
    congr 1
    apply congrArg List.ofFn
    funext j
    rw [show start+1+j.val=start+(j.val+1) by omega]

theorem deficitRangeValues_ofFn (nodes : List Executable.Node) (values : List Nat)
    (target start count : Nat) :
    deficitRangeValues nodes values target start count=List.ofFn (fun j : Fin count=>
      decide (demandRangeSum nodes target (start+j.val) 0 values<
        supplyRangeSum nodes target (start+j.val) 0 values)) := by
  induction count generalizing start with
  | zero=>rfl
  | succ count ih=>
    rw [deficitRangeValues,List.ofFn_succ,ih]
    simp only [Fin.val_zero,Nat.add_zero,Fin.val_succ]
    congr 1
    apply congrArg List.ofFn
    funext j
    rw [show start+1+j.val=start+(j.val+1) by omega]

theorem leavingRangeValues_actual (N : Nat) (vista : Executable.Vista) (weights : Array Nat)
    (length : weights.size=vista.nodes.size) (r : Nat) :
    leavingRangeValues vista.nodes.toList weights.toList (r+1) 0 (vista.nodes.size+1)=
      vectorBits (actualFields N vista weights r).leavingPositive := by
  rw [leavingRangeValues_ofFn,vectorBits]
  apply congrArg List.ofFn
  funext j
  simp [childRangeSum_vista vista weights r j.val length,actualFields,leaving,weight]

theorem deficitRangeValues_actual (N : Nat) (vista : Executable.Vista) (weights : Array Nat)
    (valid : vista.valid=true) (length : weights.size=vista.nodes.size) (r : Nat) :
    deficitRangeValues vista.nodes.toList weights.toList (r+1) 0 (vista.nodes.size+1)=
      vectorBits (actualFields N vista weights r).deficitPositive := by
  rw [deficitRangeValues_ofFn,vectorBits]
  apply congrArg List.ofFn
  funext j
  simp only [Nat.zero_add,supplyRangeSum_vista vista weights r j.val length,
    demandRangeSum_vista vista weights r j.val length (mass_sorted_of_valid vista valid),actualFields]

theorem pointRangeCheck_iff (nodes : List Executable.Node) (values : List Nat) (masks : List Bool)
    (target order visible start count : Nat) :
    pointRangeCheck nodes values masks target order visible start count=true ↔
      ∀ j : Fin count,BitGraph.bitAt masks (start+j.val)=true →
        roundBoundsCheck (childRangeSum nodes target (start+j.val) 0 values) (values[start+j.val]?.getD 0)
          (supplyRangeSum nodes target (start+j.val) 0 values)
          (demandRangeSum nodes target (start+j.val) 0 values) visible order=true := by
  induction count generalizing start with
  | zero=>simp [pointRangeCheck]
  | succ count ih=>
    rw [pointRangeCheck,Bool.and_eq_true,ih,Fin.forall_fin_succ]
    simp only [Fin.val_zero,Nat.add_zero,Fin.val_succ]
    have head (condition check : Bool) : (if condition then check else true)=true ↔
        condition=true → check=true := by cases condition <;> simp
    rw [head]
    apply and_congr Iff.rfl
    apply forall_congr'
    intro j
    rw [show start+1+j.val=start+(j.val+1) by omega]

/-- The bounded scan tests exactly the old-level nodes. The extra outside
slot is present in the physical tables but never gains an arithmetic guard. -/
theorem pointRangeCheck_levels (N : Nat) (vista : Executable.Vista) (weights : Array Nat)
    (valid : vista.valid=true) (length : weights.size=vista.nodes.size) (r : Nat) :
    pointRangeCheck vista.nodes.toList weights.toList (vectorBits (actualFields N vista weights r).isOld)
      (r+1) N (((Executable.levelNodes vista (r+1)).map (weight weights)).sum) 0 (vista.nodes.size+1)=true ↔
      ∀ u : LevelIndex vista r,
        roundBoundsCheck (childCount vista weights r u.val.val) (weight weights u.val.val)
          (supply vista weights r u.val.val) (demand vista weights r u.val.val)
          (((Executable.levelNodes vista (r+1)).map (weight weights)).sum) N=true := by
  rw [pointRangeCheck_iff]
  simp only [Nat.zero_add]
  constructor
  · intro checked u
    let j : Fin (vista.nodes.size+1) := ⟨u.val.val,by have := u.val.isLt;omega⟩
    have old : BitGraph.bitAt (vectorBits (actualFields N vista weights r).isOld) j.val=true := by
      rw [bitAt_vectorBits]
      simp [actualFields,isOld,j,u.property,u.val.isLt]
    have result := checked j old
    simpa [j,childRangeSum_vista vista weights r u.val.val length,
      supplyRangeSum_vista vista weights r u.val.val length,
      demandRangeSum_vista vista weights r u.val.val length (mass_sorted_of_valid vista valid),weight] using result
  · intro checked j old
    rw [bitAt_vectorBits] at old
    have member : j.val<vista.nodes.size ∧ (vista.node j.val).level=r := by
      simpa only [actualFields,isOld,decide_eq_true_eq] using old
    let u : LevelIndex vista r := ⟨⟨j.val,member.1⟩,member.2⟩
    have result := checked u
    simpa [u,childRangeSum_vista vista weights r j.val length,
      supplyRangeSum_vista vista weights r j.val length,
      demandRangeSum_vista vista weights r j.val length (mass_sorted_of_valid vista valid),weight] using result

theorem pointRangeCheck_verifier_component (N : Nat) (vista : Executable.Vista) (weights : Array Nat)
    (valid : vista.valid=true) (length : weights.size=vista.nodes.size) (r : Nat) :
    pointRangeCheck vista.nodes.toList weights.toList (vectorBits (actualFields N vista weights r).isOld)
      (r+1) N (((Executable.levelNodes vista (r+1)).map (weight weights)).sum) 0 (vista.nodes.size+1)=true ↔
      (∀ u : LevelIndex vista r,childCount vista weights r u.val.val ≤ weight weights u.val.val) ∧
      (hidden N vista weights r=0 → ∀ u : LevelIndex vista r,
        supply vista weights r u.val.val=demand vista weights r u.val.val) ∧
      (0<hidden N vista weights r → ∀ u : LevelIndex vista r,leaving vista weights r u.val.val=0 →
        demand vista weights r u.val.val ≤ supply vista weights r u.val.val) := by
  rw [pointRangeCheck_levels N vista weights valid length r]
  simp only [roundBoundsCheck_verifier_component,decide_eq_true_eq]
  constructor
  · intro checked
    exact ⟨fun u=>(checked u).1,fun full u=>(checked u).2.1 full,
      fun positiveHidden u=>(checked u).2.2 positiveHidden⟩
  · rintro ⟨refinement,full,positiveHidden⟩ u
    exact ⟨refinement u,fun h=>full h u,fun h=>positiveHidden h u⟩

end Counting.StackMachine.RealizabilityCheck
