import Counting.StackRealizabilityCountsShape
import Counting.RealizabilityVerifier

namespace Counting.StackMachine.RealizabilityCheck

theorem positiveCounts_array (weights : Array Nat) : positiveCounts weights.toList=true ↔
    ∀ i : Fin weights.size,0<RealizabilityVerifier.weight weights i.val:=by
  simp only [positiveCounts,List.all_eq_true,decide_eq_true_eq,List.forall_mem_iff_getElem,
    Array.length_toList,Array.getElem_toList]
  constructor
  · intro positive i
    simpa only [RealizabilityVerifier.weight,Array.getElem?_eq_getElem i.isLt,Option.getD_some] using
      positive i.val i.isLt
  · intro positive i inside
    simpa only [RealizabilityVerifier.weight,Array.getElem?_eq_getElem inside,Option.getD_some] using
      positive ⟨i,inside⟩

def countsShapeCheck (weights : Array Nat) (expected : Nat) : Bool:=
  positiveCounts weights.toList && decide (weights.size=expected)

theorem countsShapeCheck_iff (weights : Array Nat) (expected : Nat) :
    countsShapeCheck weights expected=true ↔
      weights.size=expected ∧ ∀ i : Fin expected,0<RealizabilityVerifier.weight weights i.val:=by
  simp only [countsShapeCheck,Bool.and_eq_true,decide_eq_true_eq,positiveCounts_array]
  constructor
  · rintro ⟨positive,same⟩
    refine ⟨same,?_⟩
    intro i
    exact positive ⟨i.val,by simpa only [same] using i.isLt⟩
  · rintro ⟨same,positive⟩
    refine ⟨?_,same⟩
    intro i
    exact positive ⟨i.val,by simpa only [←same] using i.isLt⟩

/-- Exactly the length and positivity component in the implemented
fixed-order verifier. No conclusion about its remaining tests is made. -/
theorem countsShapeCheck_verifier_component (vista : Executable.Vista) (weights : Array Nat) :
    countsShapeCheck weights vista.nodes.size=
      ((weights.size==vista.nodes.size) && decide
        (∀ i : Fin vista.nodes.size,0<RealizabilityVerifier.weight weights i.val)):=by
  apply Bool.eq_iff_iff.mpr
  rw [countsShapeCheck_iff]
  simp only [Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq]

theorem countsShapeCheck_of_verify (vista : Executable.Vista) (weights : Array Nat) (ell order : Nat)
    (accepted : RealizabilityVerifier.verify vista weights ell order=true) :
    countsShapeCheck weights vista.nodes.size=true:=by
  have checked:=(RealizabilityVerifier.verify_iff_checks vista weights ell order).mp accepted
  exact (countsShapeCheck_iff weights vista.nodes.size).mpr ⟨checked.length,checked.positive⟩

end Counting.StackMachine.RealizabilityCheck
