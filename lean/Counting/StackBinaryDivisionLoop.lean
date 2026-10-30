import Counting.StackBinaryDivisionBody

namespace Counting.StackMachine.Binary.Division
open Routine

def potential (divisor remainder count : Nat) : Nat := divisor+max divisor remainder+count+2

theorem potential_decreases (bit : Bool) (divisor remainder : List Bool) (count : Nat) :
    potential divisor.length (divisionRemainder bit divisor remainder).length count ≤
      potential divisor.length remainder.length (count+1) := by
  have next := divisionRemainder_length bit divisor remainder
  dsimp only [potential]
  omega

/-- The actual finite-control loop consumes exactly one dividend bit per
iteration. This quadratic length bound holds for every word, even a zero
or noncanonical divisor; the arithmetic division theorem separately uses
its explicit positive-divisor condition. -/
theorem divide_executes (input counter divisor remainder quotient : List Bool) :
    ∃ transitions ≤ 34*counter.length*potential divisor.length remainder.length counter.length+1,
      Executes routine (file input quotient divisor remainder counter [] [] [] [] []) transitions
        (file input (divideAcc counter divisor remainder quotient).1 divisor
          (divideAcc counter divisor remainder quotient).2 [] [] [] [] [] []) := by
  induction counter generalizing remainder quotient with
  | nil =>
      obtain ⟨executed,halted⟩ := bits_empty 4 body (leftControl shiftPart corePart 0) (leftControl shiftPart corePart 1)
        (file input quotient divisor remainder [] [] [] [] [] []) rfl
      exact ⟨1,by simp,⟨1,file input quotient divisor remainder [] [] [] [] [] []⟩,executed,halted,rfl⟩
  | cons bit rest ih =>
      obtain ⟨bodyTime,bodyBound,middle,bodyRun,bodyHalt,bodyStore⟩ := body_executes bit input quotient divisor remainder rest
      have consumed : Function.update (file input quotient divisor remainder (bit::rest) [] [] [] [] []) 4 rest =
          file input quotient divisor remainder rest [] [] [] [] [] := by
        funext r
        fin_cases r <;> rfl
      have firstRun := bits_iteration 4 body (leftControl shiftPart corePart 0) (leftControl shiftPart corePart 1)
        (file input quotient divisor remainder (bit::rest) [] [] [] [] []) bit rest rfl bodyTime middle
        (by simpa only [consumed] using bodyRun) bodyHalt
      obtain ⟨tailTime,tailBound,finish,tailRun,tailHalt,tailStore⟩ := ih
        (divisionRemainder bit divisor remainder) (divisionFlag bit divisor remainder::quotient)
      have decreasing := potential_decreases bit divisor remainder rest.length
      have bodyCost : bodyTime+2 ≤ 34*potential divisor.length remainder.length (rest.length+1) := by
        dsimp only [potential]
        omega
      refine ⟨bodyTime+2+tailTime,?_,finish,?_,tailHalt,?_⟩
      · have tail := Nat.mul_le_mul_left (34*rest.length) decreasing
        simp only [List.length_cons]
        nlinarith
      · rw [Machine.run_add,firstRun,Option.bind_some,bodyStore]
        exact tailRun
      · rw [tailStore]
        simp only [divideAcc]

/-- Payload-level division interface, prior to output normalization. -/
theorem divide_payloads (input dividend divisor : List Bool) :
    ∃ transitions ≤ 34*dividend.length*(2*divisor.length+dividend.length+2)+1,
      Executes routine (file input [] divisor [] dividend.reverse [] [] [] [] []) transitions
        (file input (divideBits dividend divisor).1 divisor (divideBits dividend divisor).2 [] [] [] [] [] []) := by
  simpa only [potential,List.length_nil,List.length_reverse,Nat.max_zero,divideBits,two_mul] using
    divide_executes input dividend.reverse divisor [] []

end Counting.StackMachine.Binary.Division
