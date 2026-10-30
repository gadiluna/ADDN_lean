import Counting.StackUnaryBinary
import Counting.StackRoutineBasic

/-! A single charged binary increment for level comparisons. Its bound is
in the payload bit length, even when the represented level is enormous. -/
namespace Counting.StackMachine.DagValidation
open Routine
set_option backward.isDefEq.respectTransparency false

def incrementRoutine (extra : Nat) (counter accumulator scratch : Fin (extra+3)) : Routine (extra+1) :=
  sequence (pushBit counter true) (ofProgram (Unary.toBinaryProgram extra counter accumulator scratch))

theorem increment_executes (extra : Nat) (counter accumulator scratch : Fin (extra+3))
    (ca : counter≠accumulator) (cs : counter≠scratch) (as : accumulator≠scratch)
    (store : Fin (extra+3)→List Bool) (counterEmpty : store counter=[]) (scratchEmpty : store scratch=[]) :
    Executes (incrementRoutine extra counter accumulator scratch) store
      (4*Machine.carryLength (store accumulator)+7)
      (Function.update store accumulator (Machine.increment (store accumulator))) := by
  have pushing:=pushBit_executes (registers := extra+1) counter true store
  rw [counterEmpty] at pushing
  have increment:=Unary.increment_run extra counter accumulator scratch ca cs as store [] (store accumulator) []
  simp only [List.length_nil,Nat.mul_zero,Nat.add_zero,List.replicate_zero,List.nil_append] at increment
  have cycle : Machine.run (step (Unary.toBinaryProgram extra counter accumulator scratch))
      (4*Machine.carryLength (store accumulator)+5)
      (Unary.binaryConfig extra counter accumulator scratch 0 store [true] (store accumulator) [])=
      some (Unary.binaryConfig extra counter accumulator scratch 6 store []
        (Machine.increment (store accumulator)) []) := by
    have first : Machine.run (step (Unary.toBinaryProgram extra counter accumulator scratch)) 1
        (Unary.binaryConfig extra counter accumulator scratch 0 store [true] (store accumulator) [])=
        some (Unary.binaryConfig extra counter accumulator scratch 1 store [] (store accumulator) []) := by
      rw [Machine.run,Unary.consume_bit,Option.bind_some]
      rfl
    have last : Machine.run (step (Unary.toBinaryProgram extra counter accumulator scratch)) 1
        (Unary.binaryConfig extra counter accumulator scratch 0 store [] (Machine.increment (store accumulator)) [])=
        some (Unary.binaryConfig extra counter accumulator scratch 6 store [] (Machine.increment (store accumulator)) []) := by
      rw [Machine.run,Unary.consume_empty,Option.bind_some]
      rfl
    have total : 4*Machine.carryLength (store accumulator)+5=
        (1+(4*Machine.carryLength (store accumulator)+3))+1 := by omega
    rw [total,Machine.run_add]
    rw [Machine.run_add,first,Option.bind_some,increment,Option.bind_some,last]
  have initial : Unary.binaryConfig extra counter accumulator scratch 0 store [true] (store accumulator) []=
      (⟨0,Function.update store counter [true]⟩ : Config (Unary.toBinaryProgram extra counter accumulator scratch)) := by
    apply congrArg (Config.mk _)
    funext r
    by_cases c : r=counter
    · subst r;simp
    · by_cases a : r=accumulator
      · subst r;simp [Ne.symm ca]
      · by_cases s : r=scratch
        · subst r;simp [Ne.symm cs,Ne.symm as,scratchEmpty]
        · simp [c,a,s]
  have result : (Unary.binaryConfig extra counter accumulator scratch 6 store []
      (Machine.increment (store accumulator)) []).store=
      Function.update store accumulator (Machine.increment (store accumulator)) := by
    funext r
    by_cases c : r=counter
    · subst r;simp [Unary.binaryConfig,ca,counterEmpty]
    · by_cases a : r=accumulator
      · subst r;simp [Unary.binaryConfig,Ne.symm ca]
      · by_cases s : r=scratch
        · subst r;simp [Unary.binaryConfig,Ne.symm cs,Ne.symm as,scratchEmpty]
        · simp [Unary.binaryConfig,c,a,s]
  rw [initial] at cycle
  have conversion : Executes (ofProgram (Unary.toBinaryProgram extra counter accumulator scratch))
      (Function.update store counter [true]) (4*Machine.carryLength (store accumulator)+5)
      (Function.update store accumulator (Machine.increment (store accumulator))) :=
    ⟨_,cycle,Unary.toBinary_halted _ _ _ _ _ _ _ _,result⟩
  have composed:=pushing.sequence conversion
  convert composed using 1 <;> first | rfl | omega

theorem increment_cost (bits : List Bool) :
    4*Machine.carryLength bits+7≤4*bits.length+7 := by
  have bounded:=Machine.carryLength_le bits
  omega

theorem increment_natural (extra : Nat) (counter accumulator scratch : Fin (extra+3))
    (ca : counter≠accumulator) (cs : counter≠scratch) (as : accumulator≠scratch)
    (store : Fin (extra+3)→List Bool) (counterEmpty : store counter=[]) (scratchEmpty : store scratch=[])
    (value : Nat) (encoded : store accumulator=value.bits) :
    ∃ time ≤ 4*value.size+7,Executes (incrementRoutine extra counter accumulator scratch) store time
      (Function.update store accumulator (value+1).bits) := by
  have executed:=increment_executes extra counter accumulator scratch ca cs as store counterEmpty scratchEmpty
  rw [encoded,Machine.increment_bits] at executed
  exact ⟨_,by simpa only [Encoding.bits_length] using increment_cost value.bits,executed⟩

end Counting.StackMachine.DagValidation
