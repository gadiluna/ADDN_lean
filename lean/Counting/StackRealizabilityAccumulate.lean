import Counting.StackBinaryAddRoutine
import Counting.StackNormalize
import Counting.StackEncodingUnframe
import Counting.StackEncodingCanonical
import Counting.StackEncodingRelabel
import Counting.StackUnframeCanonical

/-! A reusable charged binary accumulator for compact realizability counts.
Both operands are bit strings, never unary populations. The instruction
sequence consumes the second operand and restores its two scratch registers. -/
namespace Counting.StackMachine.RealizabilityCheck
open Routine EncodingPrograms Arithmetic
set_option backward.isDefEq.respectTransparency false

def accumulatorFile (first second reversed framed : List Bool) : Store 2:=
  ![first,second,reversed,framed]

def accumulate : Routine 2:=sequence (ofProgram (Binary.addProgram 1 0 1 2))
  (sequence (ofProgram (Normalize.reversedProgram 2 2 3))
    (ofProgram (unframeProgram 1 3 0 1)))

theorem sum_bits_length (first second : List Bool) :
    (Encoding.value first+Encoding.value second).bits.length≤first.length+second.length+1:=by
  have normalized:=normalize_length_le (addBits false first second)
  rw [normalize_eq_bits,addBits_value] at normalized
  simp only [Bool.toNat_false,Nat.add_zero] at normalized
  exact normalized.trans (addBits_length false first second)

theorem accumulate_executes (first second : List Bool) :
    ∃ time ≤ 11*(first.length+second.length)+20,
      Executes accumulate (accumulatorFile first second [] []) time
        (accumulatorFile (Encoding.value first+Encoding.value second).bits [] [] []):=by
  obtain ⟨addTime,addBound,added⟩:=binary_add_executes 1 0 1 2 (by decide) (by decide) (by decide)
    (accumulatorFile first second [] [])
  let sum:=addBits false first second
  have addStore : Function.update (Function.update (Function.update
      (accumulatorFile first second [] []) 0 []) 1 []) 2
      ((addBits false first second).reverse++[])=accumulatorFile [] [] sum.reverse []:=by
    funext r;fin_cases r <;> simp [accumulatorFile,sum]
  change Executes (ofProgram (Binary.addProgram 1 0 1 2)) (accumulatorFile first second [] []) addTime
    (Function.update (Function.update (Function.update (accumulatorFile first second [] []) 0 []) 1 []) 2
      ((addBits false first second).reverse++[])) at added
  rw [addStore] at added
  have formatted:=Normalize.reversed_executes 2 2 3 (by decide) (accumulatorFile [] [] sum.reverse [])
  have source : accumulatorFile [] [] sum.reverse [] 2=sum.reverse:=rfl
  have target : accumulatorFile [] [] sum.reverse [] 3=[]:=rfl
  rw [source,target,List.reverse_reverse,normalize_eq_bits,List.append_nil] at formatted
  have sumValue : Encoding.value sum=Encoding.value first+Encoding.value second:=by
    simp only [sum,addBits_value,Bool.toNat_false,Nat.add_zero]
  rw [sumValue] at formatted
  let result:=Encoding.value first+Encoding.value second
  have formatStore : Function.update (Function.update (accumulatorFile [] [] sum.reverse []) 2 []) 3
      (Encoding.frame result.bits)=accumulatorFile [] [] [] (Encoding.frame result.bits):=by
    funext r;fin_cases r <;> rfl
  rw [formatStore] at formatted
  let before:=accumulatorFile [] [] [] (Encoding.frame result.bits)
  have parsed:=unframe_canonical_executes 1 3 0 1 (by decide) (by decide) (by decide)
    before result.bits [] (by simp [before,accumulatorFile]) rfl
  have decoding : Executes (ofProgram (unframeProgram 1 3 0 1)) before (5*result.bits.length+2)
      (accumulatorFile result.bits [] [] []):=by
    convert parsed using 1
    funext r;fin_cases r <;> simp [before,accumulatorFile]
  have stripBound:=Normalize.stripCost_le sum.reverse
  simp only [List.length_reverse] at stripBound
  have sumBound:=addBits_length false first second
  have outputBound:=sum_bits_length first second
  change addTime≤3*(first.length+second.length)+3 at addBound
  exact ⟨_,by dsimp only [sum,result] at stripBound ⊢;omega,
    added.sequence (formatted.sequence decoding)⟩

def accumulateAt {registers : Nat} (roles : Fin 4 ↪ Fin (registers+2)) : Routine registers:=
  mapRegisters roles accumulate

theorem accumulateAt_executes {registers : Nat} (roles : Fin 4 ↪ Fin (registers+2))
    (store : Store registers) (emptyReversed : store (roles 2)=[]) (emptyFramed : store (roles 3)=[]) :
    ∃ time ≤ 11*((store (roles 0)).length+(store (roles 1)).length)+20,
      Executes (accumulateAt roles) store time
        (Function.update (Function.update store (roles 0)
          (Encoding.value (store (roles 0))+Encoding.value (store (roles 1))).bits) (roles 1) []):=by
  obtain ⟨time,bound,ran⟩:=accumulate_executes (store (roles 0)) (store (roles 1))
  refine ⟨time,bound,?_⟩
  apply relocate_executes_frame accumulate roles store _
    (accumulatorFile (store (roles 0)) (store (roles 1)) [] [])
    (accumulatorFile (Encoding.value (store (roles 0))+Encoding.value (store (roles 1))).bits [] [] [])
    time _ _ _ ran
  · funext r;fin_cases r <;> simp [accumulatorFile,emptyReversed,emptyFramed]
  · intro r;fin_cases r <;> simp [accumulatorFile,roles.injective.eq_iff,emptyReversed,emptyFramed]
  · intro r outside
    have zero : r≠roles 0:=fun equal=>outside 0 equal.symm
    have one : r≠roles 1:=fun equal=>outside 1 equal.symm
    simp [zero,one]

end Counting.StackMachine.RealizabilityCheck
