import Counting.StackRationalReduce

namespace Counting.StackMachine.RationalArithmetic
open Routine Binary EncodingPrograms

def zeroRoles : Fin 6 ↪ Fin 16 := ⟨![1,6,9,10,11,12],by decide⟩
abbrev zeroTest : Routine 14 := preservingComparison 10 zeroRoles
abbrev zeroOutput : Routine 14 := sequence (clear 3) (sequence (clear 4) (pushBit 4 true))
abbrev guardZero : Routine 14 := sequence zeroTest (branchRoutine 9 zeroOutput (skip 14))
abbrev normalizationRoutine : Routine 14 := sequence divisions guardZero

theorem zeroOutput_executes (numerator denominator common reducedNum reducedDen sign : List Bool) :
    Executes zeroOutput (file numerator denominator common reducedNum reducedDen sign)
      (reducedNum.length+reducedDen.length+5)
      (file numerator denominator common [] [true] sign) := by
  have clearNum := clear_executes (registers := 14) 3 (file numerator denominator common reducedNum reducedDen sign)
  change Executes (clear 3) (file numerator denominator common reducedNum reducedDen sign) (reducedNum.length+1)
    (Function.update (file numerator denominator common reducedNum reducedDen sign) 3 []) at clearNum
  have numStore : Function.update (file numerator denominator common reducedNum reducedDen sign) 3 [] =
      file numerator denominator common [] reducedDen sign := by
    funext r; fin_cases r <;> rfl
  rw [numStore] at clearNum
  have clearDen := clear_executes (registers := 14) 4 (file numerator denominator common [] reducedDen sign)
  change Executes (clear 4) (file numerator denominator common [] reducedDen sign) (reducedDen.length+1)
    (Function.update (file numerator denominator common [] reducedDen sign) 4 []) at clearDen
  have denStore : Function.update (file numerator denominator common [] reducedDen sign) 4 [] =
      file numerator denominator common [] [] sign := by
    funext r; fin_cases r <;> rfl
  rw [denStore] at clearDen
  have emitted := pushBit_executes (registers := 14) 4 true (file numerator denominator common [] [] sign)
  change Executes (pushBit 4 true) (file numerator denominator common [] [] sign) 1
    (Function.update (file numerator denominator common [] [] sign) 4 [true]) at emitted
  have emitStore : Function.update (file numerator denominator common [] [] sign) 4 [true] =
      file numerator denominator common [] [true] sign := by
    funext r; fin_cases r <;> rfl
  rw [emitStore] at emitted
  have composed := clearNum.sequence (clearDen.sequence emitted)
  convert composed using 1
  omega

theorem guardZero_executes (numerator denominator common reducedNum reducedDen sign : List Bool) :
    ∃ time ≤ 8*(denominator.length+reducedNum.length+reducedDen.length+3),
      Executes guardZero (file numerator denominator common reducedNum reducedDen sign) time
        (if Encoding.value denominator=0 then file numerator denominator common [] [true] sign
         else file numerator denominator common reducedNum reducedDen sign) := by
  let store := file numerator denominator common reducedNum reducedDen sign
  have compared := preservingComparison_executes 10 zeroRoles store rfl rfl rfl
  change Executes zeroTest store (preservingCompareCost denominator [])
    (Function.update store 9 [compareBits true denominator []]) at compared
  have clean : Function.update store 9 [] = store := by
    funext r; fin_cases r <;> rfl
  have flagged : Function.update (Function.update store 9 [compareBits true denominator []]) 9 [] = store := by
    rw [Function.update_idem,clean]
  have comparison : compareBits true denominator [] = true ↔ Encoding.value denominator=0 := by
    simpa [Encoding.value] using compareBits_le denominator []
  by_cases zero : Encoding.value denominator=0
  · have isZero := comparison.mpr zero
    rw [isZero] at compared
    have zeroed := zeroOutput_executes numerator denominator common reducedNum reducedDen sign
    have chosen := branch_executes_true 9 zeroOutput (skip 14)
      (Function.update store 9 [true]) (file numerator denominator common [] [true] sign) []
      (reducedNum.length+reducedDen.length+5) (by simp)
      (by rw [Function.update_idem,clean]; exact zeroed)
    refine ⟨_,?_,by simpa only [if_pos zero] using compared.sequence chosen⟩
    have bound := preservingCompareCost_le denominator []
    simp only [List.length_nil,Nat.add_zero] at bound
    omega
  · have isNonzero : compareBits true denominator [] = false := Bool.eq_false_iff.mpr (comparison.not.mpr zero)
    rw [isNonzero] at compared
    have chosen := branch_executes_false 9 zeroOutput (skip 14)
      (Function.update store 9 [false]) store [] 0 (by simp)
      (by rw [Function.update_idem,clean]; exact skip_executes store)
    refine ⟨_,?_,by simpa only [if_neg zero] using compared.sequence chosen⟩
    have bound := preservingCompareCost_le denominator []
    simp only [List.length_nil,Nat.add_zero] at bound
    omega

/-- Exact finite-stack normalization of a signed rational magnitude. The
sign is retained for final canonical signed framing; zero denominators are
explicitly mapped to magnitude zero and denominator one, as in `mkRat`.
All private registers are empty again, and both original operands survive. -/
theorem normalization_executes (numerator denominator sign : List Bool) :
    ∃ time ≤ 1400000*(numerator.length+denominator.length+1)^3,
      Executes normalizationRoutine (file numerator denominator [] [] [] sign) time
        (file numerator denominator (Nat.gcd (Encoding.value numerator) (Encoding.value denominator)).bits
          (reducedMagnitude (Encoding.value numerator) (Encoding.value denominator)).bits
          (reducedDenominator (Encoding.value numerator) (Encoding.value denominator)).bits sign) := by
  let common := Nat.gcd (Encoding.value numerator) (Encoding.value denominator)
  obtain ⟨divTime,divBound,divRan⟩ := divisions_executes numerator denominator sign
  obtain ⟨guardTime,guardBound,guardRan⟩ := guardZero_executes numerator denominator common.bits
    (Encoding.value numerator/common).bits (Encoding.value denominator/common).bits sign
  have result : (if Encoding.value denominator=0 then file numerator denominator common.bits [] [true] sign
      else file numerator denominator common.bits (Encoding.value numerator/common).bits (Encoding.value denominator/common).bits sign) =
      file numerator denominator common.bits
        (reducedMagnitude (Encoding.value numerator) (Encoding.value denominator)).bits
        (reducedDenominator (Encoding.value numerator) (Encoding.value denominator)).bits sign := by
    by_cases zero : Encoding.value denominator=0 <;> simp [reducedMagnitude,reducedDenominator,zero,common]
  rw [result] at guardRan
  refine ⟨_,?_,divRan.sequence guardRan⟩
  have a := EncodingPrograms.normalize_length_le numerator
  have b := EncodingPrograms.normalize_length_le denominator
  rw [Arithmetic.normalize_eq_bits,Encoding.bits_length] at a b
  have quotientA := Nat.size_le_size (Nat.div_le_self (Encoding.value numerator) common)
  have quotientB := Nat.size_le_size (Nat.div_le_self (Encoding.value denominator) common)
  rw [Encoding.bits_length,Encoding.bits_length] at guardBound
  have linear : numerator.length+denominator.length+1 ≤ (numerator.length+denominator.length+1)^3 := by
    have square := Nat.one_le_pow' 2 (numerator.length+denominator.length)
    have product := Nat.mul_le_mul_left (numerator.length+denominator.length+1) square
    nlinarith
  omega

end Counting.StackMachine.RationalArithmetic
