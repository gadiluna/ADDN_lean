import Counting.StackRealizabilityMaskSpec

namespace Counting.StackMachine.RealizabilityCheck
open RealizabilityVerifier RealizabilityVerifier.CompactGraph

/-- Exact list equality follows from the bounded-slot interpretation only
after the serialized vector length has also been checked. -/
theorem vectorBits_eq_of_bitAt {size : Nat} (bits : List Bool) (field : Fin size → Bool)
    (length : bits.length=size) (values : ∀ j : Fin size,BitGraph.bitAt bits j.val=field j) :
    bits=vectorBits field := by
  apply List.ext_getElem (length.trans (vectorBits_length field).symm)
  intro i hi hj
  let j : Fin size := ⟨i,by omega⟩
  have same := values j
  rw [←bitAt_vectorBits field j] at same
  simpa only [BitGraph.bitAt,j,List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem hj,Option.getD_some] using same

theorem maskSlots_old_values (N : Nat) (vista : Executable.Vista) (weights : Array Nat) (r : Nat) :
    vista.nodes.toList.map (fun node=>decide (node.level=r))++[false]=
      vectorBits (actualFields N vista weights r).isOld := by
  apply vectorBits_eq_of_bitAt
  · simp
  · exact maskSlots_old vista r

theorem maskSlots_new_values (N : Nat) (vista : Executable.Vista) (weights : Array Nat) (r : Nat) :
    vista.nodes.toList.map (fun node=>decide (node.level=r+1))++[false]=
      vectorBits (actualFields N vista weights r).isNew := by
  apply vectorBits_eq_of_bitAt
  · simp
  · exact maskSlots_new vista r

theorem maskSlots_degree_values (N : Nat) (vista : Executable.Vista) (weights : Array Nat) (r : Nat) :
    vista.nodes.toList.map (fun node=>decide (0<node.degree))++[false]=
      vectorBits (actualFields N vista weights r).degreePositive := by
  apply vectorBits_eq_of_bitAt
  · simp
  · exact maskSlots_degree vista

theorem maskSlots_outside_values (N : Nat) (vista : Executable.Vista) (weights : Array Nat) (r : Nat) :
    List.replicate vista.nodes.size false++[decide (0<hidden N vista weights r)]=
      vectorBits (actualFields N vista weights r).isOutside := by
  apply vectorBits_eq_of_bitAt
  · simp
  · intro j
    by_cases inside : j.val<vista.nodes.size
    · unfold BitGraph.bitAt
      rw [List.getElem?_append_left (by simpa using inside)]
      simp [inside,actualFields,isOutside,show j.val≠vista.nodes.size by omega]
    · have last : j.val=vista.nodes.size := by have := j.isLt;omega
      unfold BitGraph.bitAt
      rw [List.getElem?_append_right (by simp [last])]
      simp [last,actualFields,isOutside]

end Counting.StackMachine.RealizabilityCheck
