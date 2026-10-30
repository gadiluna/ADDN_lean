import Counting.StackRoutineClean

namespace Counting.StackMachine.Routine

/-- Only the registers actually cleared need a size bound. Unselected output
and input registers may be arbitrarily large and survive unchanged. The list
may contain repeats; their actual clearing instructions are still charged. -/
theorem clearRegisters_selected_executes {registers : Nat}
    (selected : List (Fin (registers+2))) (store : Store registers) (bound : Nat)
    (bounded : ∀ register∈selected,(store register).length≤bound) :
    ∃ time≤selected.length*(bound+2),
      Executes (clearRegisters selected) store time (clearedStore selected store) := by
  induction selected generalizing store with
  | nil => exact ⟨0,by simp,skip_executes store⟩
  | cons register rest ih =>
      have cleared := clear_executes register store
      have nextBound : ∀ target∈rest,((Function.update store register []) target).length≤bound := by
        intro target member
        by_cases equal : target=register
        · subst target;simp
        · simpa only [Function.update_of_ne equal] using bounded target (List.mem_cons_of_mem register member)
      obtain ⟨time,timeBound,tail⟩ := ih (Function.update store register []) nextBound
      have result : clearedStore rest (Function.update store register [])=clearedStore (register::rest) store := by
        funext target
        by_cases same : target=register <;> by_cases member : target∈rest <;>
          simp [clearedStore,Function.update,same,member]
      rw [result] at tail
      refine ⟨_,?_,cleared.sequence tail⟩
      have headBound := bounded register List.mem_cons_self
      simp only [List.length_cons]
      nlinarith

end Counting.StackMachine.Routine
