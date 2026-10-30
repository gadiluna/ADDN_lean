import Counting.AuditPrefixCounts
import Counting.RealizabilityVerifierBounds

namespace Counting.StackMachine.AuditPrefix
open Executable

def childrenPresent (vista : Vista) (level : Nat) : Bool :=
  (List.range vista.nodes.size).all (fun parent=>
    if (vista.node parent).level=level then
      decide (0<countRange vista .child (level+1) (parent+1) 0 vista.nodes.size) else true)

def countFlat (vista : Vista) (level : Nat) : Bool :=
  decide (0<level) && decide (0<countRange vista .level (level-1) 0 0 vista.nodes.size) &&
    (List.range vista.nodes.size).all (fun parent=>
      if (vista.node parent).level=level-1 then
        decide (countRange vista .child level (parent+1) 0 vista.nodes.size=1) else true)

theorem childrenPresent_eq (vista : Vista) (level : Nat) :
    childrenPresent vista level=
      (levelNodes vista level).all (fun i=>!(children vista i (level+1)).isEmpty) := by
  simp only [childrenPresent,levelNodes,List.all_filter]
  apply congrArg (fun predicate : Nat→Bool=>(List.range vista.nodes.size).all predicate)
  funext parent
  rw [countRange_full_children]
  by_cases selected : (vista.node parent).level=level
  · apply Bool.eq_iff_iff.mpr
    simp [selected,Nat.pos_iff_ne_zero]
  · simp [selected]

theorem countFlat_eq (vista : Vista) (level : Nat) : countFlat vista level=flat vista level := by
  simp only [countFlat,countRange_full_level,flat]
  have nonempty : decide (0<(levelNodes vista (level-1)).length)=
      !(levelNodes vista (level-1)).isEmpty := by
    apply Bool.eq_iff_iff.mpr
    simp [Nat.pos_iff_ne_zero]
  rw [nonempty]
  congr 1
  simp only [levelNodes,List.all_filter]
  apply congrArg (fun predicate : Nat→Bool=>(List.range vista.nodes.size).all predicate)
  funext parent
  rw [countRange_full_children]
  by_cases selected : (vista.node parent).level=level-1 <;>
    apply Bool.eq_iff_iff.mpr <;> simp [selected]

def openingAccepted (vista : Vista) (leaders candidate last : Nat) : Bool :=
  vista.valid && decide (0<leaders) && decide (leaders≤candidate) &&
    decide (0<last) && decide (last≤(vista.node vista.bottom).level)

def countsPrefix? (vista : Vista) (candidate last : Nat) : Option Nat := do
  if countRange vista .leader 0 0 0 vista.nodes.size=0 then none else do
    if !(List.range (last+1)).all (fun level=>
        countRange vista .level level 0 0 vista.nodes.size≤candidate) then none else do
      if !(List.range last).all (childrenPresent vista) then none else
        ((List.range (last+1)).reverse).find? (countFlat vista)

/-- The paid node-count implementation has exactly the same prefix
conditions and anchor-selection order as the executable audit. -/
theorem auditPrefix_eq_counts (vista : Vista) (leaders candidate last : Nat) :
    auditPrefix? vista leaders candidate last=
      if openingAccepted vista leaders candidate last then countsPrefix? vista candidate last else none := by
  have first : (!vista.valid || leaders==0 || candidate<leaders || last==0 ||
      (vista.node vista.bottom).level<last)=!openingAccepted vista leaders candidate last := by
    apply Bool.eq_iff_iff.mpr
    simp [openingAccepted]
  have leader : (countRange vista .leader 0 0 0 vista.nodes.size=0) ↔
      (!(levelNodes vista 0).any (fun i=>(vista.node i).leader))=true := by
    have positive:=countRange_leader_positive vista 0 0
    cases seen:(levelNodes vista 0).any (fun i=>(vista.node i).leader) with
    | false=>
      have zero : countRange vista .leader 0 0 0 vista.nodes.size=0 := by
        rw [seen] at positive
        simp only [Bool.false_eq_true,iff_false] at positive
        omega
      simp [zero]
    | true=>
      have nonzero : countRange vista .leader 0 0 0 vista.nodes.size≠0 := Nat.ne_of_gt (positive.mpr seen)
      simp [nonzero]
  have flatPred : countFlat vista=flat vista := funext (countFlat_eq vista)
  have childPred : childrenPresent vista=fun r=>(levelNodes vista r).all
      (fun i=>!(children vista i (r+1)).isEmpty) := funext (childrenPresent_eq vista)
  simp only [auditPrefix?,first,countsPrefix?,countRange_full_level,flatPred,childPred,leader]
  cases openingAccepted vista leaders candidate last <;> rfl

/-- The bound for all following round loops is derived from the checked
DAG and bottom label, never from an external population-size parameter. -/
theorem openingAccepted_bounds (vista : Vista) (leaders candidate last : Nat)
    (accepted : openingAccepted vista leaders candidate last=true) :
    vista.valid=true ∧ 0<leaders ∧ leaders≤candidate ∧ 0<last ∧
      last≤(vista.node vista.bottom).level ∧ last+1≤vista.nodes.size := by
  simp only [openingAccepted,Bool.and_eq_true,decide_eq_true_eq] at accepted
  obtain ⟨⟨⟨⟨valid,positive⟩,candidateBound⟩,lastPositive⟩,depth⟩:=accepted
  have bounded:=RealizabilityVerifier.valid_depth_lt_size vista valid
  exact ⟨valid,positive,candidateBound,lastPositive,depth,by omega⟩

end Counting.StackMachine.AuditPrefix
