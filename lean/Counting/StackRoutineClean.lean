import Counting.StackRoutineBasic
import Counting.StackRoutineRelocate

namespace Counting.StackMachine.Routine

def clearRegisters {registers : Nat} : List (Fin (registers+2)) → Routine registers
  | [] => skip registers
  | register::rest => sequence (clear register) (clearRegisters rest)

def clearedStore {registers : Nat} (selected : List (Fin (registers+2)))
    (store : Store registers) : Store registers :=
  fun register => if register ∈ selected then [] else store register

theorem clearRegisters_executes {registers : Nat} (selected : List (Fin (registers+2)))
    (store : Store registers) (bound : Nat) (bounded : ∀ register, (store register).length ≤ bound) :
    ∃ time ≤ selected.length*(bound+2),
      Executes (clearRegisters selected) store time (clearedStore selected store) := by
  induction selected generalizing store with
  | nil => exact ⟨0,by simp,skip_executes store⟩
  | cons register rest ih =>
      have cleared := clear_executes register store
      have nextBound : ∀ target, ((Function.update store register []) target).length ≤ bound := by
        intro target
        by_cases equal : target = register
        · subst target; simp
        · simpa only [Function.update_of_ne equal] using bounded target
      obtain ⟨time,timeBound,tail⟩ := ih (Function.update store register []) nextBound
      have result : clearedStore rest (Function.update store register []) = clearedStore (register::rest) store := by
        funext target
        by_cases same : target=register <;> by_cases member : target∈rest <;>
          simp [clearedStore,Function.update,same,member]
      rw [result] at tail
      refine ⟨_,?_,cleared.sequence tail⟩
      have headBound := bounded register
      simp only [List.length_cons]
      nlinarith

def workRegisters (registers : Nat) : List (Fin (registers+2)) :=
  (List.finRange (registers+2)).filter (· ≠ 1)

def isolate {registers : Nat} (routine : Routine registers) : Routine registers :=
  sequence routine (clearRegisters (workRegisters registers))

def inputStore (registers : Nat) (input : List Bool) : Store registers :=
  fun register => if register=0 then input else []

def outputStore (registers : Nat) (output : List Bool) : Store registers :=
  fun register => if register=1 then output else []

theorem computed_length_le {registers : Nat} (routine : Routine registers)
    (function : List Bool → List Bool) (bound : Nat → Nat)
    (computes : ComputesIn routine.program function bound) (input : List Bool) :
    (function input).length ≤ input.length+bound input.length := by
  obtain ⟨time,finish,timeBound,⟨ran,_⟩,result⟩ := computes input
  have dataBound := run_dataLength (initial routine.program input) finish time ran
  rw [initial_dataLength] at dataBound
  have outputBound : (finish.store 1).length ≤ finish.dataLength :=
    Finset.single_le_sum (f := fun register => (finish.store register).length)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ 1)
  rw [result] at outputBound
  omega

/-- Every executable transducer can be used as a reusable subroutine. All
working registers, including its consumed input, are explicitly erased;
the extra transitions are charged using the proved stack-growth bound. -/
theorem isolate_executes {registers : Nat} (routine : Routine registers)
    (function : List Bool → List Bool) (bound : Nat → Nat)
    (computes : ComputesIn routine.program function bound) (input : List Bool) :
    ∃ time ≤ (registers+3)*(bound input.length+input.length+3),
      Executes (isolate routine) (inputStore registers input) time
        (outputStore registers (function input)) := by
  obtain ⟨time,finish,timeBound,⟨ran,halted⟩,result⟩ := computes input
  have dataBound := run_dataLength (initial routine.program input) finish time ran
  rw [initial_dataLength] at dataBound
  have registerBound (register : Fin (registers+2)) : (finish.store register).length ≤ input.length+time := by
    have bounded : (finish.store register).length ≤ finish.dataLength :=
      Finset.single_le_sum (f := fun register => (finish.store register).length)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ register)
    exact bounded.trans dataBound
  obtain ⟨clearTime,clearBound,cleared⟩ := clearRegisters_executes (workRegisters registers)
    finish.store (input.length+time) registerBound
  have finalStore : clearedStore (workRegisters registers) finish.store = outputStore registers (function input) := by
    funext register
    by_cases output : register=1
    · subst register; simpa [clearedStore,workRegisters,outputStore] using result
    · simp [clearedStore,workRegisters,outputStore,output]
  rw [finalStore] at cleared
  have executed : Executes routine (inputStore registers input) time finish.store :=
    ⟨finish,ran,halted,rfl⟩
  refine ⟨_,?_,executed.sequence cleared⟩
  have selectedLength : (workRegisters registers).length ≤ registers+2 := by
    exact (List.length_filter_le _ _).trans_eq (by simp)
  have boundClear := Nat.mul_le_mul_right (input.length+time+2) selectedLength
  have total := Nat.mul_le_mul_left (registers+3) timeBound
  nlinarith

end Counting.StackMachine.Routine
