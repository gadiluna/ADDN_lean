import Counting.StackRoutineSemantics

namespace Counting.StackMachine.Routine

abbrev skip (registers : Nat) : Routine registers := ⟨0,fun _ => .halt⟩

theorem skip_executes (store : Store registers) : Executes (skip registers) store 0 store :=
  ⟨⟨0,store⟩,rfl,rfl,rfl⟩

abbrev pushBit {registers : Nat} (target : Fin (registers+2)) (bit : Bool) : Routine registers :=
  ⟨1,fun control => if control = 0 then .push target bit 1 else .halt⟩

theorem pushBit_executes (target : Fin (registers+2)) (bit : Bool) (store : Store registers) :
    Executes (pushBit target bit) store 1 (Function.update store target (bit::store target)) := by
  refine ⟨⟨1,Function.update store target (bit::store target)⟩,?_,?_,rfl⟩
  · simp [Machine.run,step,pushBit]
  · simp [step,pushBit]

abbrev clear (target : Fin (registers+2)) : Routine registers :=
  ⟨1,fun control => if control = 0 then .pop target 1 0 0 else .halt⟩

theorem clear_executes (target : Fin (registers+2)) (store : Store registers) :
    Executes (clear target) store ((store target).length+1) (Function.update store target []) := by
  generalize content : store target = bits
  induction bits generalizing store with
  | nil =>
      have changed : Function.update store target [] = store := by rw [← content,Function.update_eq_self]
      refine ⟨⟨1,store⟩,?_,?_,changed.symm⟩
      · simp [Machine.run,step,clear,content]
      · simp [step,clear]
  | cons bit bits ih =>
      obtain ⟨finish,ran,halted,result⟩ := ih (Function.update store target bits) (by simp)
      refine ⟨finish,?_,halted,?_⟩
      · have first : step (clear target).program (⟨0,store⟩ : Config (clear target).program) =
            some ⟨0,Function.update store target bits⟩ := by simp [step,clear,content]
        rw [List.length_cons,Machine.run,first,Option.bind_some]
        exact ran
      · simpa only [Function.update_idem] using result

/-- A fixed word is compiled into pushes and charged jumps. This is code
generation at compile time, not a free runtime list operation. -/
def prepend (target : Fin (registers+2)) : List Bool → Routine registers
  | [] => skip registers
  | bit::rest => sequence (prepend target rest) (pushBit target bit)

theorem prepend_executes (target : Fin (registers+2)) (word : List Bool) (store : Store registers) :
    Executes (prepend target word) store (2*word.length) (Function.update store target (word++store target)) := by
  induction word generalizing store with
  | nil => simpa only [prepend,List.length_nil,Nat.mul_zero,List.nil_append,Function.update_eq_self] using skip_executes store
  | cons bit rest ih =>
      have combined := (ih store).sequence (pushBit_executes target bit (Function.update store target (rest++store target)))
      simpa only [prepend,List.length_cons,List.cons_append,Function.update_self,Function.update_idem,
        show 2*(rest.length+1) = 2*rest.length+1+1 by omega] using combined

end Counting.StackMachine.Routine
