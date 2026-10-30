import Counting.StackBinaryGcdReduce

namespace Counting.StackMachine.Binary.Gcd
open Routine EncodingPrograms

def zeroRoles : Fin 6 ↪ Fin 10 where
  toFun := ![2,3,5,7,8,9]
  inj' := by decide

abbrev zeroTest : Routine 8 := preservingComparison 4 zeroRoles
abbrev body : Routine 8 := sequence zeroTest (branchRoutine 5 (skip 8) reduce)
abbrev routine : Routine 8 := forEach 0 body

theorem body_executes (counter : List Bool) (first second : Nat) :
    ∃ transitions ≤ 250*(first.size+second.size+1)^2,
      Executes body (file counter first second) transitions
        (if second=0 then file counter first second else file counter second (first%second)) := by
  have compared := preservingComparison_executes 4 zeroRoles (file counter first second) rfl rfl rfl
  change Executes zeroTest (file counter first second) (preservingCompareCost second.bits [])
    (Function.update (file counter first second) 5 [compareBits true second.bits []]) at compared
  have cleaned (flag : Bool) : Function.update (Function.update (file counter first second) 5 [flag]) 5 [] =
      file counter first second := by
    rw [Function.update_idem]
    have empty : file counter first second 5 = [] := rfl
    rw [← empty,Function.update_eq_self]
  have cost := preservingCompareCost_le second.bits []
  simp only [Encoding.bits_length,List.length_nil,Nat.add_zero] at cost
  have zeroSpec := compareBits_le second.bits []
  simp only [Encoding.value_bits,Encoding.value,Nat.le_zero] at zeroSpec
  have square : first.size+second.size+1 ≤ (first.size+second.size+1)^2 := by
    simpa only [pow_two] using Nat.le_mul_self (first.size+second.size+1)
  by_cases zero : second=0
  · have flag := zeroSpec.mpr zero
    rw [flag] at compared
    have chosen := branch_executes_true 5 (skip 8) reduce
      (Function.update (file counter first second) 5 [true]) (file counter first second) [] 0
      (by simp) (by rw [cleaned]; exact skip_executes _)
    refine ⟨_,?_,by simpa only [if_pos zero] using compared.sequence chosen⟩
    omega
  · have flag : compareBits true second.bits [] = false :=
      Bool.eq_false_iff.mpr (fun h => zero (zeroSpec.mp h))
    rw [flag] at compared
    obtain ⟨reduceTime,reduceBound,reduced⟩ := reduce_executes counter first second (by omega)
    have chosen := branch_executes_false 5 (skip 8) reduce
      (Function.update (file counter first second) 5 [false]) (file counter second (first%second)) [] reduceTime
      (by simp) (by rw [cleaned]; exact reduced)
    refine ⟨_,?_,by simpa only [if_neg zero] using compared.sequence chosen⟩
    omega

end Counting.StackMachine.Binary.Gcd
