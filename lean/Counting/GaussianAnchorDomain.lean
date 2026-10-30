import Counting.ExecutableRefinementAnchor
import Counting.LabelBoundsAnchor

namespace Counting.Executable

/-- Anchor rows contain integer coefficients even for an arbitrary
syntactically supplied DAG; validity and physical provenance are only
needed for the stronger size bounds. -/
theorem anchorRows_integral_coefficient (vista : Vista) (anchor leaders : Nat)
    (row : Equation) (member : row∈anchorRows vista anchor leaders)
    (coefficient : Rat) (present : coefficient∈row.1.toList) : coefficient.den=1 := by
  unfold anchorRows at member
  rcases List.mem_append.mp member with flow | normalize
  · obtain ⟨old,_,rfl⟩ := List.mem_map.mp flow
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp present
    exact (rational_difference_labels (countFrom (vista.node i) old)
      (if (vista.node i).parent==some old then (vista.node i).degree else 0)).1
  · have equal : row=((levelNodes vista anchor |>.map
        (fun i=>if (vista.node i).leader then (1:Rat) else 0)).toArray,(leaders:Rat)) := by
      simpa only [List.mem_singleton] using normalize
    rw [equal] at present
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp present
    cases (vista.node i).leader <;> simp

theorem anchorRows_integral (vista : Vista) (anchor leaders width : Nat) :
    (∀ r i,(rowMatrix width (anchorRows vista anchor leaders) r i).den=1) ∧
    (∀ r,(rowRhs (anchorRows vista anchor leaders) r).den=1) := by
  constructor
  · intro r i
    unfold rowMatrix
    cases found : ((anchorRows vista anchor leaders).get r).1[i.val]? with
    | none => simp
    | some value =>
      simp only [Option.getD_some]
      exact anchorRows_integral_coefficient vista anchor leaders _ (List.get_mem _ r) value
        (Array.mem_toList_iff.mpr (Array.mem_of_getElem? found))
  · intro r
    exact (anchorRows_rhs vista anchor leaders _ (List.get_mem _ r)).1

end Counting.Executable
