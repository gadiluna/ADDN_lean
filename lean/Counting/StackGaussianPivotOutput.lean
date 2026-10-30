import Counting.StackGaussianPivotCorrectness
import Counting.StackRoutineUnary
import Counting.StackEncodingFrame
import Counting.EncodingDag

namespace Counting.StackMachine.GaussianPivot
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

abbrev binaryResult : Routine 29 := ofProgram (Unary.toBinaryProgram 28 1 3 4)
abbrev frameResult : Routine 29 := frameRoutine 28 3 1 4
abbrev formatNone : Routine 29 := sequence (clear 1) frameResult
abbrev formatSome : Routine 29 := sequence binaryResult frameResult
abbrev formatResult : Routine 29 := branchRead 30 formatNone formatSome

def done (matrix output : List Bool) (column : Nat) (exhausted : Bool) : Fin 31 → List Bool :=
  file matrix output (List.replicate (column+1) true) [] [] [] [] [] [] [exhausted]

theorem frameResult_executes (matrix : List Bool) (value column : Nat) (exhausted : Bool) :
    Executes frameResult
      (file matrix [] (List.replicate (column+1) true) value.bits [] [] [] [] [] [exhausted])
      (5*value.bits.length+4) (done matrix (Encoding.natural.encode value) column exhausted) := by
  have ran := frame_executes_updates 28 (3 : Fin 31) 1 4 (by decide) (by decide) (by decide)
    (file matrix [] (List.replicate (column+1) true) value.bits [] [] [] [] [] [exhausted]) rfl
  convert ran using 1
  · rfl
  funext r;fin_cases r <;> simp [done,file,Encoding.natural]

/-- Format the actual search result with the same optional-natural codec
used elsewhere: zero encodes failure and `index+1` encodes success. -/
theorem formatResult_executes (matrix : List Bool) (index column : Nat) (exhausted : Bool) :
    ∃ time ≤ 20*(index+2)^2,
      Executes formatResult (state matrix index column [] exhausted) time
        (done matrix (Encoding.optionalNatural.encode (if exhausted then none else some index)) column exhausted) := by
  cases exhausted
  · obtain ⟨binaryTime,binaryBound,binary⟩ := toBinary_executes 28 (1 : Fin 31) 3 4
      (by decide) (by decide) (by decide) (state matrix index column [] false) 0 rfl rfl
    have binaryResult : Function.update (Function.update (state matrix index column [] false) 1 []) 3
        (0+(state matrix index column [] false 1).length).bits=
        file matrix [] (List.replicate (column+1) true) (index+1).bits [] [] [] [] [] [false] := by
      funext r;fin_cases r <;> simp [state,file]
    rw [binaryResult] at binary
    have framed := frameResult_executes matrix (index+1) column false
    have combined := binary.sequence framed
    have branch := branchRead_executes (30 : Fin 31) formatNone formatSome false [] _ _ _ rfl combined
    refine ⟨binaryTime+1+(5*(index+1).bits.length+4)+3,?_,?_⟩
    · have bits : (index+1).bits.length ≤ index+1 := by rw [Encoding.bits_length];exact Nat.size_le.mpr Nat.lt_two_pow_self
      simp [state,file] at binaryBound
      nlinarith
    · simpa only [Bool.false_eq_true,if_false,Encoding.optionalNatural,Encoding.transport,Option.map_some,Option.getD_some] using branch
  · have cleared := clear_executes (1 : Fin 31) (state matrix index column [] true)
    have clearedResult : Function.update (state matrix index column [] true) 1 []=
        file matrix [] (List.replicate (column+1) true) (0 : Nat).bits [] [] [] [] [] [true] := by
      funext r;fin_cases r <;> simp [state,file]
    rw [clearedResult] at cleared
    have timeEq : (state matrix index column [] true 1).length+1=index+2 := by simp [state,file]
    rw [timeEq] at cleared
    have framed := frameResult_executes matrix 0 column true
    have combined := cleared.sequence framed
    have branch := branchRead_executes (30 : Fin 31) formatNone formatSome true [] _ _ _ rfl combined
    refine ⟨index+2+1+4+3,?_,?_⟩
    · nlinarith
    · simpa [Encoding.optionalNatural,Encoding.transport] using branch

end Counting.StackMachine.GaussianPivot
