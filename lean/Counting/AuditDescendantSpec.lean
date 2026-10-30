import Counting.Executable

namespace Counting.Executable

def descendantSelected (vista : Vista) (steps last ancestor descendant : Nat) : Bool :=
  decide ((vista.node descendant).level=last) && decide (ascend vista steps descendant=some ancestor)

def descendantCountRange (vista : Vista) (steps last ancestor start count : Nat) : Nat :=
  ((List.range' start count).filter (descendantSelected vista steps last ancestor)).length

@[simp] theorem descendantCountRange_zero (vista : Vista) (steps last ancestor start : Nat) :
    descendantCountRange vista steps last ancestor start 0=0 := rfl

theorem descendantCountRange_succ (vista : Vista) (steps last ancestor start count : Nat) :
    descendantCountRange vista steps last ancestor start (count+1)=
      (if descendantSelected vista steps last ancestor start then 1 else 0)+
        descendantCountRange vista steps last ancestor (start+1) count := by
  simp only [descendantCountRange,List.range'_succ,List.filter_cons]
  cases descendantSelected vista steps last ancestor start <;> simp [Nat.add_comm]

theorem descendantCountRange_le (vista : Vista) (steps last ancestor start count : Nat) :
    descendantCountRange vista steps last ancestor start count ≤ count := by
  exact (List.length_filter_le _ _).trans_eq List.length_range'

def auditDescendantAt (vista : Vista) (weights : Array Nat) (anchor last ancestor : Nat) : Bool :=
  decide (descendantCountRange vista (last-anchor) last ancestor 0 vista.nodes.size ≤
    weights[ancestor]?.getD 0)

def auditDescendants (vista : Vista) (weights : Array Nat) (anchor last : Nat) : Bool :=
  (List.range vista.nodes.size).all (fun ancestor=>
    if (vista.node ancestor).level=anchor then auditDescendantAt vista weights anchor last ancestor else true)

theorem descendantCountRange_full (vista : Vista) (steps last ancestor : Nat) :
    descendantCountRange vista steps last ancestor 0 vista.nodes.size=
      ((levelNodes vista last).filter (fun descendant=>ascend vista steps descendant==some ancestor)).length := by
  unfold descendantCountRange levelNodes
  rw [←List.range_eq_range',List.filter_filter]
  congr 2
  funext descendant
  apply Bool.eq_iff_iff.mpr
  simp [descendantSelected,and_comm]

/-- The finite source and target scans implement the literal last check
of the executable audit, with truncated subtraction preserved exactly. -/
theorem auditDescendants_eq (vista : Vista) (weights : Array Nat) (anchor last : Nat) :
    auditDescendants vista weights anchor last=
      (levelNodes vista anchor).all (fun ancestor=>
        ((levelNodes vista last).filter (fun descendant=>
          ascend vista (last-anchor) descendant==some ancestor)).length ≤ weights[ancestor]?.getD 0) := by
  simp only [auditDescendants,levelNodes,List.all_filter]
  apply congrArg (fun predicate : Nat→Bool=>(List.range vista.nodes.size).all predicate)
  funext ancestor
  rw [auditDescendantAt,descendantCountRange_full]
  by_cases selected : (vista.node ancestor).level=anchor <;> simp [selected,levelNodes]

end Counting.Executable
