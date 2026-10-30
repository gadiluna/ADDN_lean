import Counting.StackRoutineClean

namespace Counting.StackMachine.Routine

/-- Pointwise isolation charges the erasure of every private register.
It needs only the concrete run on this input, so a canonical-input
transducer need not be extended by an unproved malformed-input contract. -/
theorem isolate_halts {registers : Nat} (routine : Routine registers)
    (input output : List Bool) (limit : Nat)
    (halts : ∃ time last,time≤ limit ∧ HaltsAt routine.program input time last ∧ last.store 1=output) :
    ∃ time ≤ (registers+3)*(limit+input.length+3),
      Executes (isolate routine) (inputStore registers input) time (outputStore registers output) := by
  obtain ⟨time,last,timeBound,⟨ran,halted⟩,result⟩ := halts
  have dataBound := run_dataLength (initial routine.program input) last time ran
  rw [initial_dataLength] at dataBound
  have registerBound (register : Fin (registers+2)) : (last.store register).length≤ input.length+time := by
    have localBound : (last.store register).length≤ last.dataLength :=
      Finset.single_le_sum (f:=fun register=>(last.store register).length)
        (fun _ _=>Nat.zero_le _) (Finset.mem_univ register)
    exact localBound.trans dataBound
  obtain ⟨clearTime,clearBound,cleared⟩ := clearRegisters_executes (workRegisters registers)
    last.store (input.length+time) registerBound
  have finalStore : clearedStore (workRegisters registers) last.store=outputStore registers output := by
    funext register
    by_cases atOutput : register=1
    · subst register;simpa [clearedStore,workRegisters,outputStore] using result
    · simp [clearedStore,workRegisters,outputStore,atOutput]
  rw [finalStore] at cleared
  have executed : Executes routine (inputStore registers input) time last.store := ⟨last,ran,halted,rfl⟩
  refine ⟨_,?_,executed.sequence cleared⟩
  have selectedLength : (workRegisters registers).length≤ registers+2 :=
    (List.length_filter_le _ _).trans_eq (by simp)
  have boundClear := Nat.mul_le_mul_right (input.length+time+2) selectedLength
  have total := Nat.mul_le_mul_left (registers+3) timeBound
  nlinarith

end Counting.StackMachine.Routine
