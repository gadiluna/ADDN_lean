import Counting.StackSignedBits
import Counting.StackBinaryAddRoutine
import Counting.StackBinarySubtractRoutine
import Counting.StackBinaryComparePreserving
import Counting.StackRoutineBasic
import Counting.StackEncodingBranch

namespace Counting.StackMachine.Signed
open Routine Binary

set_option backward.isDefEq.respectTransparency false

/-- Sign registers 8/9 are consumed by the outer branch. Register 10 holds
the result sign; register 11 holds a temporary comparison. -/
def file (input first second firstSign secondSign result resultSign reversed flag : List Bool) :
    Fin 12 → List Bool :=
  ![input,result,first,second,[],[],reversed,[],firstSign,secondSign,resultSign,flag]

abbrev sumPart : Routine 10 := sequence
  (ofProgram (Binary.addProgram 9 2 3 6))
  (ofProgram (ListPrograms.reverseProgram 10 6 1))

def firstIndex (reverse : Bool) : Fin 12 := if reverse then 3 else 2
def secondIndex (reverse : Bool) : Fin 12 := if reverse then 2 else 3

abbrev differencePart (reverse : Bool) : Routine 10 := sequence
  (ofProgram (Binary.subtractProgram 9 (firstIndex reverse) (secondIndex reverse) 6))
  (ofProgram (ListPrograms.reverseProgram 10 6 1))

def compareRoles : Fin 6 ↪ Fin 12 where
  toFun := ![2,3,11,4,5,7]
  inj' := by decide

abbrev comparePart : Routine 10 := preservingComparison 6 compareRoles

theorem sum_executes (input first second : List Bool) :
    ∃ transitions ≤ 5*(first.length+second.length)+7,
      Executes sumPart (file input first second [] [] [] [] [] []) transitions
        (file input [] [] [] [] (Arithmetic.addBits false first second) [] [] []) := by
  obtain ⟨time,bounded,added⟩ := binary_add_executes 9 2 3 6 (by decide) (by decide) (by decide)
    (file input first second [] [] [] [] [] [])
  change Executes (ofProgram (Binary.addProgram 9 2 3 6))
    (file input first second [] [] [] [] [] []) time
    (Function.update (Function.update (Function.update (file input first second [] [] [] [] [] []) 2 []) 3 []) 6
      ((Arithmetic.addBits false first second).reverse++[])) at added
  have afterAdd : Function.update (Function.update (Function.update (file input first second [] [] [] [] [] []) 2 []) 3 []) 6
      ((Arithmetic.addBits false first second).reverse++[]) =
      file input [] [] [] [] [] [] (Arithmetic.addBits false first second).reverse [] := by
    funext r; fin_cases r <;> simp [file]
  simp +instances only [Binary.addProgram] at added
  rw [afterAdd] at added
  have reversed := reverse_executes 10 6 1 (by decide)
    (file input [] [] [] [] [] [] (Arithmetic.addBits false first second).reverse [])
  change Executes (ofProgram (ListPrograms.reverseProgram 10 6 1))
    (file input [] [] [] [] [] [] (Arithmetic.addBits false first second).reverse [])
    (2*(Arithmetic.addBits false first second).reverse.length+1)
    (Function.update (Function.update (file input [] [] [] [] [] [] (Arithmetic.addBits false first second).reverse []) 6 []) 1
      ((Arithmetic.addBits false first second).reverse.reverse++[])) at reversed
  have afterReverse : Function.update (Function.update
      (file input [] [] [] [] [] [] (Arithmetic.addBits false first second).reverse []) 6 []) 1
      ((Arithmetic.addBits false first second).reverse.reverse++[]) =
      file input [] [] [] [] (Arithmetic.addBits false first second) [] [] [] := by
    funext r; fin_cases r <;> simp [file]
  simp +instances only [ListPrograms.reverseProgram] at reversed
  rw [afterReverse] at reversed
  refine ⟨_,?_,added.sequence reversed⟩
  change time ≤ 3*(first.length+second.length)+3 at bounded
  have length := Arithmetic.addBits_length false first second
  simp only [List.length_reverse]
  omega

theorem difference_executes (reverse : Bool) (input first second : List Bool) :
    Executes (differencePart reverse) (file input first second [] [] [] [] [] [])
      (5*max first.length second.length+4)
      (file input [] [] [] []
        (subtractBits false (if reverse then second else first) (if reverse then first else second)).1 [] [] []) := by
  have distinct : firstIndex reverse ≠ secondIndex reverse := by cases reverse <;> decide
  have firstOut : firstIndex reverse ≠ 6 := by cases reverse <;> decide
  have secondOut : secondIndex reverse ≠ 6 := by cases reverse <;> decide
  have subtracted := binary_subtract_executes 9 (firstIndex reverse) (secondIndex reverse) 6
    distinct firstOut secondOut (file input first second [] [] [] [] [] [])
  have firstAt : file input first second [] [] [] [] [] [] (firstIndex reverse) =
      if reverse then second else first := by cases reverse <;> rfl
  have secondAt : file input first second [] [] [] [] [] [] (secondIndex reverse) =
      if reverse then first else second := by cases reverse <;> rfl
  rw [firstAt,secondAt] at subtracted
  let result := (subtractBits false (if reverse then second else first) (if reverse then first else second)).1
  change Executes (ofProgram (Binary.subtractProgram 9 (firstIndex reverse) (secondIndex reverse) 6))
    (file input first second [] [] [] [] [] [])
    (3*max (if reverse then second else first).length (if reverse then first else second).length+2)
    (Function.update (Function.update (Function.update (file input first second [] [] [] [] [] [])
      (firstIndex reverse) []) (secondIndex reverse) []) 6 (result.reverse++[])) at subtracted
  have afterSubtract : Function.update (Function.update (Function.update
      (file input first second [] [] [] [] [] []) (firstIndex reverse) []) (secondIndex reverse) []) 6
      (result.reverse++[]) = file input [] [] [] [] [] [] result.reverse [] := by
    funext r; cases reverse <;> fin_cases r <;> simp [file,firstIndex,secondIndex]
  simp +instances only [Binary.subtractProgram] at subtracted
  rw [afterSubtract] at subtracted
  have reversed := reverse_executes 10 6 1 (by decide) (file input [] [] [] [] [] [] result.reverse [])
  change Executes (ofProgram (ListPrograms.reverseProgram 10 6 1))
    (file input [] [] [] [] [] [] result.reverse []) (2*result.reverse.length+1)
    (Function.update (Function.update (file input [] [] [] [] [] [] result.reverse []) 6 []) 1
      (result.reverse.reverse++[])) at reversed
  have afterReverse : Function.update (Function.update (file input [] [] [] [] [] [] result.reverse []) 6 []) 1
      (result.reverse.reverse++[]) = file input [] [] [] [] result [] [] [] := by
    funext r; fin_cases r <;> simp [file]
  simp +instances only [ListPrograms.reverseProgram] at reversed
  rw [afterReverse] at reversed
  have composed := subtracted.sequence reversed
  have length : result.length = max first.length second.length := by
    dsimp only [result]
    rw [subtractBits_length]
    cases reverse <;> simp [max_comm]
  rw [List.length_reverse,length] at composed
  have cost : 3*max (if reverse then second else first).length
      (if reverse then first else second).length+2+1+(2*max first.length second.length+1) =
      5*max first.length second.length+4 := by
    cases reverse <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega
  rw [cost] at composed
  exact composed

theorem compare_executes (input first second : List Bool) :
    Executes comparePart (file input first second [] [] [] [] [] [])
      (preservingCompareCost first second)
      (file input first second [] [] [] [] [] [compareBits true first second]) := by
  have compared := preservingComparison_executes 6 compareRoles
    (file input first second [] [] [] [] [] []) rfl rfl rfl
  change Executes comparePart (file input first second [] [] [] [] [] [])
    (preservingCompareCost first second)
    (Function.update (file input first second [] [] [] [] [] []) 11 [compareBits true first second]) at compared
  have afterCompare : Function.update (file input first second [] [] [] [] [] []) 11 [compareBits true first second] =
      file input first second [] [] [] [] [] [compareBits true first second] := by
    funext r; fin_cases r <;> rfl
  rw [afterCompare] at compared
  exact compared

theorem sign_executes (sign : Bool) (input magnitude : List Bool) :
    Executes (pushBit (registers := 10) 10 sign) (file input [] [] [] [] magnitude [] [] []) 1
      (file input [] [] [] [] magnitude [sign] [] []) := by
  have executed := pushBit_executes (registers := 10) 10 sign (file input [] [] [] [] magnitude [] [] [])
  have finish : Function.update (file input [] [] [] [] magnitude [] [] []) 10 [sign] =
      file input [] [] [] [] magnitude [sign] [] [] := by
    funext r; fin_cases r <;> rfl
  change Executes _ _ 1 (Function.update (file input [] [] [] [] magnitude [] [] []) 10 [sign]) at executed
  rw [finish] at executed
  exact executed

end Counting.StackMachine.Signed
