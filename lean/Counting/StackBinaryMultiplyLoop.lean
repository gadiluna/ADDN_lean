import Counting.StackBinaryMultiplyBody

namespace Counting.StackMachine.Binary
open Arithmetic Routine

/-- An invariant potential depending only on bit lengths. -/
def multiplyPotential (count shifted accumulator : Nat) : Nat :=
  accumulator+count*(shifted+count+1)+shifted+count+2

theorem potential_decreases (count : Nat) (shifted accumulator : List Bool) (bit : Bool) :
    multiplyPotential count (false::shifted).length
        (if bit then addBits false accumulator shifted else accumulator).length ≤
      multiplyPotential (count+1) shifted.length accumulator.length := by
  have added : (if bit then addBits false accumulator shifted else accumulator).length ≤
      accumulator.length+shifted.length+1 := by
    cases bit
    · simp only [Bool.false_eq_true,if_false]; omega
    · exact addBits_length false accumulator shifted
  simp only [multiplyPotential,List.length_cons]
  nlinarith

/-- The actual finite loop executes one branch per multiplier bit, with
all temporary registers empty between iterations. -/
theorem multiply_executes (input multiplier shifted accumulator : List Bool) :
    ∃ transitions ≤ 12*multiplier.length*
        multiplyPotential multiplier.length shifted.length accumulator.length+1,
      Executes multiplyRoutine (file input accumulator shifted multiplier [] [] []) transitions
        (file input (multiplyAcc multiplier shifted accumulator)
          (List.replicate multiplier.length false++shifted) [] [] [] []) := by
  induction multiplier generalizing shifted accumulator with
  | nil =>
      obtain ⟨executed,halted⟩ := bits_empty 3 multiplyBody (rightControl preparePart shiftPart 0) 0
        (file input accumulator shifted [] [] [] []) rfl
      exact ⟨1,by simp,⟨1,file input accumulator shifted [] [] [] []⟩,executed,halted,rfl⟩
  | cons bit rest ih =>
      let nextAccumulator := if bit then addBits false accumulator shifted else accumulator
      obtain ⟨bodySteps,bodyBound,middle,bodyRun,bodyHalt,bodyStore⟩ :=
        body_executes bit input accumulator shifted rest
      have consumed : Function.update (file input accumulator shifted (bit::rest) [] [] []) 3 rest =
          file input accumulator shifted rest [] [] [] := by
        funext r
        fin_cases r <;> rfl
      have firstRun := bits_iteration 3 multiplyBody (rightControl preparePart shiftPart 0) 0
        (file input accumulator shifted (bit::rest) [] [] []) bit rest rfl bodySteps middle
        (by simpa only [consumed] using bodyRun) bodyHalt
      obtain ⟨tailSteps,tailBound,finish,tailRun,tailHalt,tailStore⟩ := ih (false::shifted) nextAccumulator
      have decreasing := potential_decreases rest.length shifted accumulator bit
      have bodyCost : bodySteps+2 ≤ 12*multiplyPotential (rest.length+1) shifted.length accumulator.length := by
        dsimp [multiplyPotential]
        nlinarith
      refine ⟨(bodySteps+2)+tailSteps,?_,finish,?_,tailHalt,?_⟩
      · have tail := Nat.mul_le_mul_left (12*rest.length) decreasing
        simp only [List.length_cons] at tail ⊢
        dsimp [nextAccumulator] at tailBound
        nlinarith
      · rw [Machine.run_add,firstRun,Option.bind_some,bodyStore]
        exact tailRun
      · rw [tailStore]
        simp only [multiplyAcc,List.length_cons,List.replicate_succ',List.append_assoc,
          List.singleton_append]
        rfl

theorem multiply_payloads (first second suffix : List Bool) :
    ∃ transitions ≤ 12*second.length*
        (second.length*(first.length+second.length+1)+first.length+second.length+2)+1,
      Executes multiplyRoutine (file suffix [] first second [] [] []) transitions
        (file suffix (multiplyBits first second) (List.replicate second.length false++first) [] [] [] []) := by
  simpa only [multiplyPotential,List.length_nil,Nat.zero_add,multiplyBits] using
    multiply_executes suffix second first []

end Counting.StackMachine.Binary
