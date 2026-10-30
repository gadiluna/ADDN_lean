import Counting.StackBinaryDivisionBits
import Counting.StackBinaryComparePreserving
import Counting.StackBinarySubtractRoutine
import Counting.StackEncodingBranch
import Counting.StackBitLoop

namespace Counting.StackMachine.Binary.Division
open Routine

/-- Input suffix, quotient, divisor, remainder, unprocessed dividend bits,
branch flag, two operand copies, copy scratch, and reversed difference. -/
def file (input quotient divisor remainder counter flag left right scratch reversed : List Bool) : Fin 10 → List Bool :=
  fun r => match r.val with
    | 0 => input | 1 => quotient | 2 => divisor | 3 => remainder | 4 => counter
    | 5 => flag | 6 => left | 7 => right | 8 => scratch | _ => reversed

def roles : Fin 6 ↪ Fin 10 where
  toFun := ![2,3,5,6,7,8]
  inj' := by decide

abbrev comparePart : Routine 8 := preservingComparison 4 roles
abbrev copyPart : Routine 8 := ofProgram (ListPrograms.copyProgram 7 2 6 8)
abbrev subtractPart : Routine 8 := ofProgram (subtractProgram 7 3 6 9)
abbrev reversePart : Routine 8 := ofProgram (ListPrograms.reverseProgram 8 9 3)

def emitPart (bit : Bool) : Routine 8 where
  states := 1
  code state := if state = 0 then .push 1 bit 1 else .halt

abbrev differencePart : Routine 8 := sequence copyPart (sequence subtractPart reversePart)
abbrev yesPart : Routine 8 := sequence differencePart (emitPart true)
abbrev noPart : Routine 8 := emitPart false
abbrev choosePart : Routine 8 := EncodingPrograms.branchRoutine 5 yesPart noPart
abbrev corePart : Routine 8 := sequence comparePart choosePart

def shiftPart : Routine 8 where
  states := 2
  code state := match state.val with
    | 0 => .push 3 false 2
    | 1 => .push 3 true 2
    | _ => .halt

abbrev body : Routine 8 := sequence shiftPart corePart
abbrev routine : Routine 8 := forBits 4 body (leftControl shiftPart corePart 0) (leftControl shiftPart corePart 1)

theorem emit_executes (bit : Bool) (input quotient divisor remainder counter : List Bool) :
    Executes (emitPart bit) (file input quotient divisor remainder counter [] [] [] [] []) 1
      (file input (bit::quotient) divisor remainder counter [] [] [] [] []) := by
  refine ⟨⟨1,file input (bit::quotient) divisor remainder counter [] [] [] [] []⟩,?_,rfl,rfl⟩
  apply congrArg some
  apply congrArg (Config.mk _)
  funext r
  fin_cases r <;> rfl

theorem compare_executes (input quotient divisor remainder counter : List Bool) :
    Executes comparePart (file input quotient divisor remainder counter [] [] [] [] [])
      (preservingCompareCost divisor remainder)
      (file input quotient divisor remainder counter [compareBits true divisor remainder] [] [] [] []) := by
  have executed := preservingComparison_executes 4 roles
    (file input quotient divisor remainder counter [] [] [] [] []) rfl rfl rfl
  change Executes comparePart (file input quotient divisor remainder counter [] [] [] [] [])
    (preservingCompareCost divisor remainder)
    (Function.update (file input quotient divisor remainder counter [] [] [] [] []) 5 [compareBits true divisor remainder]) at executed
  have finish : Function.update (file input quotient divisor remainder counter [] [] [] [] []) 5 [compareBits true divisor remainder] =
      file input quotient divisor remainder counter [compareBits true divisor remainder] [] [] [] [] := by
    funext r
    fin_cases r <;> rfl
  rw [finish] at executed
  exact executed

theorem difference_executes (input quotient divisor remainder counter : List Bool) :
    Executes differencePart (file input quotient divisor remainder counter [] [] [] [] [])
      ((5*divisor.length+2)+1+((3*max remainder.length divisor.length+2)+1+(2*max remainder.length divisor.length+1)))
      (file input quotient divisor (subtractBits false remainder divisor).1 counter [] [] [] [] []) := by
  have copied := copy_executes 7 2 6 8 (by decide) (by decide) (by decide)
    (file input quotient divisor remainder counter [] [] [] [] []) rfl
  change Executes copyPart (file input quotient divisor remainder counter [] [] [] [] []) (5*divisor.length+2)
    (Function.update (file input quotient divisor remainder counter [] [] [] [] []) 6 (divisor++[])) at copied
  have copyFinish : Function.update (file input quotient divisor remainder counter [] [] [] [] []) 6 (divisor++[]) =
      file input quotient divisor remainder counter [] divisor [] [] [] := by
    funext r
    fin_cases r <;> simp [file]
  rw [copyFinish] at copied
  have subtracted := binary_subtract_executes 7 3 6 9 (by decide) (by decide) (by decide)
    (file input quotient divisor remainder counter [] divisor [] [] [])
  change Executes subtractPart (file input quotient divisor remainder counter [] divisor [] [] [])
    (3*max remainder.length divisor.length+2)
    (Function.update (Function.update (Function.update (file input quotient divisor remainder counter [] divisor [] [] []) 3 []) 6 []) 9
      ((subtractBits false remainder divisor).1.reverse++[])) at subtracted
  have subFinish : Function.update (Function.update (Function.update (file input quotient divisor remainder counter [] divisor [] [] []) 3 []) 6 []) 9
      ((subtractBits false remainder divisor).1.reverse++[]) =
      file input quotient divisor [] counter [] [] [] [] (subtractBits false remainder divisor).1.reverse := by
    funext r
    fin_cases r <;> simp [file]
  rw [subFinish] at subtracted
  have reversed := reverse_executes 8 9 3 (by decide)
    (file input quotient divisor [] counter [] [] [] [] (subtractBits false remainder divisor).1.reverse)
  change Executes reversePart (file input quotient divisor [] counter [] [] [] [] (subtractBits false remainder divisor).1.reverse)
    (2*(subtractBits false remainder divisor).1.reverse.length+1)
    (Function.update (Function.update (file input quotient divisor [] counter [] [] [] [] (subtractBits false remainder divisor).1.reverse) 9 []) 3
      ((subtractBits false remainder divisor).1.reverse.reverse++[])) at reversed
  have reverseFinish : Function.update (Function.update (file input quotient divisor [] counter [] [] [] [] (subtractBits false remainder divisor).1.reverse) 9 []) 3
      ((subtractBits false remainder divisor).1.reverse.reverse++[]) =
      file input quotient divisor (subtractBits false remainder divisor).1 counter [] [] [] [] [] := by
    funext r
    fin_cases r <;> simp [file]
  rw [reverseFinish,List.length_reverse,subtractBits_length] at reversed
  exact copied.sequence (subtracted.sequence reversed)

theorem core_executes (bit : Bool) (input quotient divisor remainder counter : List Bool) :
    ∃ transitions ≤ 30*(divisor.length+remainder.length+2),
      Executes corePart (file input quotient divisor (bit::remainder) counter [] [] [] [] []) transitions
        (file input (divisionFlag bit divisor remainder::quotient) divisor
          (divisionRemainder bit divisor remainder) counter [] [] [] [] []) := by
  have compared := compare_executes input quotient divisor (bit::remainder) counter
  have cleaned (flag : Bool) : Function.update
      (file input quotient divisor (bit::remainder) counter [flag] [] [] [] []) 5 [] =
      file input quotient divisor (bit::remainder) counter [] [] [] [] [] := by
    funext r
    fin_cases r <;> rfl
  have compareBound := preservingCompareCost_le divisor (bit::remainder)
  by_cases enough : divisionFlag bit divisor remainder = true
  · have difference := difference_executes input quotient divisor (bit::remainder) counter
    have emitted := emit_executes true input quotient divisor (subtractBits false (bit::remainder) divisor).1 counter
    have chosen := EncodingPrograms.branch_executes_true 5 yesPart noPart
      (file input quotient divisor (bit::remainder) counter [true] [] [] [] [])
      (file input (true::quotient) divisor (subtractBits false (bit::remainder) divisor).1 counter [] [] [] [] []) []
      _ rfl (by rw [cleaned]; exact difference.sequence emitted)
    change compareBits true divisor (bit::remainder) = true at enough
    rw [enough] at compared
    refine ⟨_,?_,by simpa only [divisionRemainder,divisionFlag,enough,ite_true] using compared.sequence chosen⟩
    simp only [List.length_cons] at compareBound ⊢
    omega
  · have absent : compareBits true divisor (bit::remainder) = false := by
      change ¬compareBits true divisor (bit::remainder) = true at enough
      exact Bool.eq_false_iff.mpr enough
    have chosen := EncodingPrograms.branch_executes_false 5 yesPart noPart
      (file input quotient divisor (bit::remainder) counter [false] [] [] [] [])
      (file input (false::quotient) divisor (bit::remainder) counter [] [] [] [] []) [] 1 rfl
      (by rw [cleaned]; exact emit_executes false input quotient divisor (bit::remainder) counter)
    rw [absent] at compared
    refine ⟨_,?_,by simpa only [divisionRemainder,divisionFlag,absent,Bool.false_eq_true,ite_false] using compared.sequence chosen⟩
    simp only [List.length_cons] at compareBound
    omega

theorem body_executes (bit : Bool) (input quotient divisor remainder counter : List Bool) :
    ∃ transitions ≤ 32*(divisor.length+remainder.length+2), ∃ finish : Config body.program,
      Machine.run (step body.program) transitions
        ⟨if bit then leftControl shiftPart corePart 1 else leftControl shiftPart corePart 0,
          file input quotient divisor remainder counter [] [] [] [] []⟩ = some finish ∧
      step body.program finish = none ∧
      finish.store = file input (divisionFlag bit divisor remainder::quotient) divisor
        (divisionRemainder bit divisor remainder) counter [] [] [] [] [] := by
  obtain ⟨coreTime,coreBound,finish,executed,halted,stored⟩ := core_executes bit input quotient divisor remainder counter
  have shifted : step shiftPart.program
      (⟨if bit then 1 else 0,file input quotient divisor remainder counter [] [] [] [] []⟩ : Config shiftPart.program) =
      some ⟨2,file input quotient divisor (bit::remainder) counter [] [] [] [] []⟩ := by
    cases bit <;> apply congrArg some <;> apply congrArg (Config.mk _) <;> funext r <;> fin_cases r <;> rfl
  have transfer : Machine.run (step body.program) 2
      (leftConfig shiftPart corePart ⟨if bit then 1 else 0,file input quotient divisor remainder counter [] [] [] [] []⟩) =
      some (rightConfig shiftPart corePart ⟨0,file input quotient divisor (bit::remainder) counter [] [] [] [] []⟩) := by
    rw [Machine.run,left_step shiftPart corePart _ _ shifted,Option.bind_some,Machine.run,
      left_halt shiftPart corePart _ (by rfl),Option.bind_some]
    rfl
  refine ⟨2+coreTime,by omega,rightConfig shiftPart corePart finish,?_,?_,stored⟩
  · have start : (⟨if bit then leftControl shiftPart corePart 1 else leftControl shiftPart corePart 0,
          file input quotient divisor remainder counter [] [] [] [] []⟩ : Config body.program) =
        leftConfig shiftPart corePart ⟨if bit then 1 else 0,file input quotient divisor remainder counter [] [] [] [] []⟩ := by
      cases bit <;> rfl
    rw [start,Machine.run_add,transfer,Option.bind_some,right_run,executed]
    rfl
  · rw [right_step,halted]
    rfl

end Counting.StackMachine.Binary.Division
