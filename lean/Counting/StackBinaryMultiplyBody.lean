import Counting.StackBinaryAddRoutine
import Counting.StackBinaryMultiplyBits
import Counting.StackBitLoop

namespace Counting.StackMachine.Binary
open Arithmetic Routine

/-- Register file: unused input suffix, product, shifted multiplicand,
remaining multiplier, copy operand, copy scratch, and reversed sum. -/
def file (input accumulator shifted multiplier operand scratch reversed : List Bool) : Fin 7 → List Bool :=
  fun r => match r.val with
    | 0 => input | 1 => accumulator | 2 => shifted | 3 => multiplier
    | 4 => operand | 5 => scratch | _ => reversed

abbrev copyPart : Routine 5 := ofProgram (ListPrograms.copyProgram 4 2 4 5)
abbrev addPart : Routine 5 := ofProgram (addProgram 4 1 4 6)
abbrev reversePart : Routine 5 := ofProgram (ListPrograms.reverseProgram 5 6 1)
abbrev sumPart : Routine 5 := sequence addPart reversePart
abbrev preparePart : Routine 5 := sequence copyPart sumPart

def shiftPart : Routine 5 where
  states := 1
  code state := if state = 0 then .push 2 false 1 else .halt

abbrev multiplyBody : Routine 5 := sequence preparePart shiftPart
abbrev multiplyRoutine : Routine 5 :=
  forBits 3 multiplyBody (rightControl preparePart shiftPart 0) 0

theorem shift_executes (input accumulator shifted multiplier : List Bool) :
    Executes shiftPart (file input accumulator shifted multiplier [] [] []) 1
      (file input accumulator (false::shifted) multiplier [] [] []) := by
  refine ⟨⟨1,file input accumulator (false::shifted) multiplier [] [] []⟩,?_,rfl,rfl⟩
  apply congrArg some
  apply congrArg (Config.mk _)
  funext r
  fin_cases r <;> rfl

theorem sum_executes (input accumulator shifted multiplier : List Bool) :
    ∃ transitions ≤ 5*(accumulator.length+shifted.length)+7,
      Executes sumPart (file input accumulator shifted multiplier shifted [] []) transitions
        (file input (addBits false accumulator shifted) shifted multiplier [] [] []) := by
  obtain ⟨addSteps,addBound,added⟩ := binary_add_executes 4 1 4 6 (by decide) (by decide) (by decide)
    (file input accumulator shifted multiplier shifted [] [])
  have afterAdd : Function.update (Function.update (Function.update
        (file input accumulator shifted multiplier shifted [] []) 1 []) 4 []) 6
        ((addBits false accumulator shifted).reverse++[]) =
      file input [] shifted multiplier [] [] (addBits false accumulator shifted).reverse := by
    funext r
    fin_cases r <;> simp [file]
  change Executes addPart (file input accumulator shifted multiplier shifted [] []) addSteps
    (Function.update (Function.update (Function.update
      (file input accumulator shifted multiplier shifted [] []) 1 []) 4 []) 6
      ((addBits false accumulator shifted).reverse++[])) at added
  rw [afterAdd] at added
  have reversed := reverse_executes 5 6 1 (by decide)
    (file input [] shifted multiplier [] [] (addBits false accumulator shifted).reverse)
  have afterReverse : Function.update (Function.update
        (file input [] shifted multiplier [] [] (addBits false accumulator shifted).reverse) 6 []) 1
        ((addBits false accumulator shifted).reverse.reverse++[]) =
      file input (addBits false accumulator shifted) shifted multiplier [] [] [] := by
    funext r
    fin_cases r <;> simp [file]
  change Executes reversePart (file input [] shifted multiplier [] [] (addBits false accumulator shifted).reverse)
    (2*(addBits false accumulator shifted).reverse.length+1)
    (Function.update (Function.update
      (file input [] shifted multiplier [] [] (addBits false accumulator shifted).reverse) 6 []) 1
      ((addBits false accumulator shifted).reverse.reverse++[])) at reversed
  rw [afterReverse] at reversed
  have composed := added.sequence reversed
  refine ⟨addSteps+1+(2*(addBits false accumulator shifted).reverse.length+1),?_,composed⟩
  change addSteps ≤ 3*(accumulator.length+shifted.length)+3 at addBound
  have length := addBits_length false accumulator shifted
  simp only [List.length_reverse]
  omega

theorem prepare_executes (input accumulator shifted multiplier : List Bool) :
    ∃ transitions ≤ 5*accumulator.length+10*shifted.length+10,
      Executes preparePart (file input accumulator shifted multiplier [] [] []) transitions
        (file input (addBits false accumulator shifted) shifted multiplier [] [] []) := by
  have copied := copy_executes 4 2 4 5 (by decide) (by decide) (by decide)
    (file input accumulator shifted multiplier [] [] []) (by rfl)
  have afterCopy : Function.update (file input accumulator shifted multiplier [] [] []) 4 (shifted++[]) =
      file input accumulator shifted multiplier shifted [] [] := by
    funext r
    fin_cases r <;> simp [file]
  change Executes copyPart (file input accumulator shifted multiplier [] [] []) (5*shifted.length+2)
    (Function.update (file input accumulator shifted multiplier [] [] []) 4 (shifted++[])) at copied
  rw [afterCopy] at copied
  obtain ⟨sumSteps,sumBound,summed⟩ := sum_executes input accumulator shifted multiplier
  refine ⟨(5*shifted.length+2)+1+sumSteps,by omega,copied.sequence summed⟩

theorem body_true_executes (input accumulator shifted multiplier : List Bool) :
    ∃ transitions ≤ 5*accumulator.length+10*shifted.length+12,
      Executes multiplyBody (file input accumulator shifted multiplier [] [] []) transitions
        (file input (addBits false accumulator shifted) (false::shifted) multiplier [] [] []) := by
  obtain ⟨prepareSteps,prepareBound,prepared⟩ := prepare_executes input accumulator shifted multiplier
  refine ⟨prepareSteps+1+1,by omega,prepared.sequence (shift_executes _ _ _ _)⟩

/-- The body branch is chosen by the bit actually popped from the multiplier. -/
theorem body_executes (bit : Bool) (input accumulator shifted multiplier : List Bool) :
    ∃ transitions ≤ 10*(accumulator.length+shifted.length+2),
      ∃ finish : Config multiplyBody.program,
        Machine.run (step multiplyBody.program) transitions
          ⟨if bit then 0 else rightControl preparePart shiftPart 0,
            file input accumulator shifted multiplier [] [] []⟩ = some finish ∧
        step multiplyBody.program finish = none ∧
        finish.store = file input (if bit then addBits false accumulator shifted else accumulator)
          (false::shifted) multiplier [] [] [] := by
  cases bit with
  | true =>
      obtain ⟨transitions,bounded,finish,executed,halted,stored⟩ := body_true_executes input accumulator shifted multiplier
      exact ⟨transitions,by omega,finish,executed,halted,stored⟩
  | false =>
      obtain ⟨finish,executed,halted,stored⟩ := shift_executes input accumulator shifted multiplier
      refine ⟨1,by omega,rightConfig preparePart shiftPart finish,?_,?_,stored⟩
      · exact (right_run preparePart shiftPart 1 ⟨0,file input accumulator shifted multiplier [] [] []⟩).trans
          (by rw [executed]; rfl)
      · rw [right_step,halted]
        rfl

end Counting.StackMachine.Binary
