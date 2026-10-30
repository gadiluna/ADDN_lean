import Counting.StackRowDotBounds
import Counting.StackRowAddInput

namespace Counting.StackMachine.RowDot
open Routine RowAdd

abbrev complete : Routine 34 := sequence prepareInput (sequence dotRoutine (move 33 2 1 7))
abbrev inputCodec := RowAdd.inputCodec

theorem complete_halts (pairs : List (Rat×Rat)) :
    ∃ steps output,
      steps ≤ 100000000000000*((inputCodec.encode (pairs.map Prod.fst,pairs.map Prod.snd)).length+1)^4 ∧
      HaltsAt complete.program (inputCodec.encode (pairs.map Prod.fst,pairs.map Prod.snd)) steps output ∧
      output.store 1 = Encoding.rational.encode ((pairs.map (fun pair => pair.1*pair.2)).sum) := by
  let input := inputCodec.encode (pairs.map Prod.fst,pairs.map Prod.snd)
  let first := Encoding.rationalRow.encode (pairs.map Prod.fst)
  let second := Encoding.rationalRow.encode (pairs.map Prod.snd)
  let result := Encoding.rational.encode ((pairs.map (fun pair => pair.1*pair.2)).sum)
  have prepared := prepareInput_executes (pairs.map Prod.fst) (pairs.map Prod.snd)
  obtain ⟨dotTime,dotBound,dotted⟩ := dot_executes_polynomial pairs [] []
  simp only [List.append_nil,List.length_nil,Nat.add_zero] at dotted dotBound
  have moved := move_executes 33 2 1 7 (by decide) (by decide) (by decide)
    (file [] [] result [] [] [] [] [] [] [] []) rfl
  have movedStore : Function.update (Function.update (file [] [] result [] [] [] [] [] [] [] []) 1 (result++[])) 2 [] =
      file [] result [] [] [] [] [] [] [] [] [] := by
    funext r; fin_cases r <;> simp [file]
  change Executes _ _ (6*result.length+4)
    (Function.update (Function.update (file [] [] result [] [] [] [] [] [] [] []) 1 (result++[])) 2 []) at moved
  rw [movedStore] at moved
  obtain ⟨middle,middleRun,_,middleStore⟩ := prepared.sequence dotted
  have startMiddle : initial (sequence prepareInput dotRoutine).program input = ⟨0,file input [] [] [] [] [] [] [] [] [] []⟩ := by
    apply congrArg (Config.mk _)
    funext r; fin_cases r <;> simp [file]
  have dataBound := run_dataLength (initial (sequence prepareInput dotRoutine).program input) middle
    (6*input.length+5*first.length+6*second.length+12+1+dotTime) (by rw [startMiddle]; exact middleRun)
  rw [initial_dataLength] at dataBound
  have outputBound : result.length ≤ middle.dataLength := by
    have entry := Finset.single_le_sum (f := fun register => (middle.store register).length)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ (2 : Register (sequence prepareInput dotRoutine).program))
    have outputEntry : middle.store 2 = result := by
      rw [middleStore]
      simp [file,result]
    rw [← outputEntry]
    exact entry
  obtain ⟨last,ran,halted,stored⟩ := prepared.sequence (dotted.sequence moved)
  refine ⟨6*input.length+5*first.length+6*second.length+12+1+(dotTime+1+(6*result.length+4)),last,?_,⟨?_,halted⟩,?_⟩
  · have inputLength : input.length = 2*first.length+1+second.length := by
      change (Encoding.frame first++second).length = _
      rw [List.length_append,Encoding.frame_length]
    have power := Nat.pow_le_pow_left (show first.length+second.length+1 ≤ input.length+1 by omega) 4
    change dotTime ≤ 10000000000000*(first.length+second.length+1)^4 at dotBound
    have linear : input.length+1 ≤ (input.length+1)^4 := by
      have cube := Nat.one_le_pow' 3 input.length
      have product := Nat.mul_le_mul_left (input.length+1) cube
      nlinarith
    change _ ≤ 100000000000000*(input.length+1)^4
    omega
  · have start : initial complete.program input = ⟨0,file input [] [] [] [] [] [] [] [] [] []⟩ := by
      apply congrArg (Config.mk _)
      funext r; fin_cases r <;> simp [file]
    rw [start]
    exact ran
  · rw [stored]
    simp [file,result]

end Counting.StackMachine.RowDot
