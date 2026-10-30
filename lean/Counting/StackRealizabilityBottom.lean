import Counting.StackRealizabilityOne
import Counting.StackRealizabilityCountsSpec
import Counting.DagClosureCriterion

namespace Counting.StackMachine.RealizabilityCheck
open Routine

theorem valid_bottom_last (vista : Executable.Vista) (valid : vista.valid=true) :
    vista.bottom+1=vista.nodes.size:=by
  have inside : vista.bottom<vista.nodes.size:=by
    simp only [Executable.Vista.valid,Bool.and_eq_true,decide_eq_true_eq] at valid
    exact valid.1.1.1
  exact (Executable.backwardCover_of_allReachable vista (Executable.topological_of_valid vista valid)
    inside (Executable.allReachable_of_valid vista valid)).1

/-- In a valid topological DAG the final stored entry is the bottom. The
explicit array count therefore supplies the field index without converting
an unbounded binary number to unary. -/
theorem countOneGuard_bottom_spec (vista : Executable.Vista) (valid : vista.valid=true)
    (weights : Array Nat) (length : weights.size=vista.nodes.size) :
    FieldAccess.selectPayload ((Encoding.list Encoding.natural).encode weights.toList) weights.size=some [true] ↔
      RealizabilityVerifier.weight weights vista.bottom=1:=by
  have last : vista.bottom+1=weights.size:=(valid_bottom_last vista valid).trans length.symm
  have inside : vista.bottom<weights.size:=by omega
  rw [←last,countOneGuard_naturalList]
  have listInside : vista.bottom<weights.toList.length:=by simpa only [Array.length_toList] using inside
  simp only [List.getElem?_eq_getElem listInside,Option.some.injEq,Array.getElem_toList,
    RealizabilityVerifier.weight,Array.getElem?_eq_getElem inside,Option.getD_some]

theorem countOneGuard_bottom_executes (store : Store 7) (accepted : Bool) (tail : List Bool)
    (status : store 2=accepted::tail) (empty : ∀ r : Fin 9,3≤r.val → store r=[])
    (vista : Executable.Vista) (valid : vista.valid=true) (weights : Array Nat)
    (length : weights.size=vista.nodes.size)
    (input : store 0=(Encoding.list Encoding.natural).encode weights.toList)
    (index : (store 1).length=weights.size) :
    ∃ time ≤ 60*((store 0).length+weights.size+1),
      Executes countOneGuard store time (Function.update store 2
        ((accepted && decide (RealizabilityVerifier.weight weights vista.bottom=1))::tail)):=by
  obtain ⟨time,bound,ran⟩:=countOneGuard_executes store accepted tail status empty
  rw [index] at bound ran
  simp only [input,countOneGuard_bottom_spec vista valid weights length] at ran
  exact ⟨time,bound,ran⟩

end Counting.StackMachine.RealizabilityCheck
