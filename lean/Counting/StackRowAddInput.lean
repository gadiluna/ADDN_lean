import Counting.StackRowAddBounds

namespace Counting.StackMachine.RowAdd
open Routine EncodingPrograms

abbrev prepareInput : Routine 34 := sequence (move 33 0 2 7)
  (sequence (ofProgram (unframeProgram 33 2 0 7)) (move 33 2 1 7))
abbrev complete : Routine 34 := sequence prepareInput (sequence addRoutine (move 33 2 1 7))
def inputCodec : Encoding.Codec (List Rat×List Rat) :=
  Encoding.product (Encoding.framed Encoding.rationalRow) Encoding.rationalRow

theorem prepareInput_executes (left right : List Rat) :
    Executes prepareInput (file (inputCodec.encode (left,right)) [] [] [] [] [] [] [] [] [] [])
      (6*(inputCodec.encode (left,right)).length+5*(Encoding.rationalRow.encode left).length+
        6*(Encoding.rationalRow.encode right).length+12)
      (file (Encoding.rationalRow.encode left) (Encoding.rationalRow.encode right) [] [] [] [] [] [] [] [] []) := by
  let input := inputCodec.encode (left,right)
  let first := Encoding.rationalRow.encode left
  let second := Encoding.rationalRow.encode right
  have moved := move_executes 33 0 2 7 (by decide) (by decide) (by decide) (file input [] [] [] [] [] [] [] [] [] []) rfl
  have movedStore : Function.update (Function.update (file input [] [] [] [] [] [] [] [] [] []) 2 (input++[])) 0 [] =
      file [] [] input [] [] [] [] [] [] [] [] := by
    funext r; fin_cases r <;> simp [file]
  change Executes _ _ (6*input.length+4)
    (Function.update (Function.update (file input [] [] [] [] [] [] [] [] [] []) 2 (input++[])) 0 []) at moved
  rw [movedStore] at moved
  let base := file [] [] input [] [] [] [] [] [] [] []
  have start : unframeConfig 33 2 0 7 0 base (Encoding.frame first++second) [] [] =
      (⟨0,base⟩ : Config (unframeProgram 33 2 0 7)) := by
    apply congrArg (Config.mk _)
    change (fun r : Fin 36 => _) = base
    funext r; fin_cases r <;> simp [base,input,first,second,inputCodec,Encoding.product,Encoding.framed,file]
  have ran := unframe_frames 33 2 0 7 (by decide) (by decide) (by decide) base first second []
  rw [start] at ran
  have parsedRun : Executes (ofProgram (unframeProgram 33 2 0 7)) base (5*first.length+2)
      (file first [] second [] [] [] [] [] [] [] []) := by
    refine ⟨unframeConfig 33 2 0 7 7 base second (first++[]) [],ran,(unframe_halted _ _ _ _ _ _ _ _).1,?_⟩
    change (fun r : Fin 36 => _) = _
    funext r; fin_cases r <;> simp [unframeConfig,base,file]
  have delivered := move_executes 33 2 1 7 (by decide) (by decide) (by decide)
    (file first [] second [] [] [] [] [] [] [] []) rfl
  have deliveredStore : Function.update (Function.update (file first [] second [] [] [] [] [] [] [] []) 1 (second++[])) 2 [] =
      file first second [] [] [] [] [] [] [] [] [] := by
    funext r; fin_cases r <;> simp [file]
  change Executes _ _ (6*second.length+4)
    (Function.update (Function.update (file first [] second [] [] [] [] [] [] [] []) 1 (second++[])) 2 []) at delivered
  rw [deliveredStore] at delivered
  have combined := moved.sequence (parsedRun.sequence delivered)
  change Executes prepareInput (file input [] [] [] [] [] [] [] [] [] [])
    (6*input.length+4+1+(5*first.length+2+1+(6*second.length+4)))
    (file first second [] [] [] [] [] [] [] [] []) at combined
  convert combined using 1
  change 6*input.length+5*first.length+6*second.length+12 = 6*input.length+4+1+(5*first.length+2+1+(6*second.length+4))
  omega

theorem complete_halts (pairs : List (Rat×Rat)) :
    ∃ steps output,
      steps ≤ 10000000000*((inputCodec.encode (pairs.map Prod.fst,pairs.map Prod.snd)).length+1)^4 ∧
      HaltsAt complete.program (inputCodec.encode (pairs.map Prod.fst,pairs.map Prod.snd)) steps output ∧
      output.store 1 = Encoding.rationalRow.encode (pairs.map (fun pair => pair.1+pair.2)) := by
  let input := inputCodec.encode (pairs.map Prod.fst,pairs.map Prod.snd)
  let first := Encoding.rationalRow.encode (pairs.map Prod.fst)
  let second := Encoding.rationalRow.encode (pairs.map Prod.snd)
  let result := Encoding.rationalRow.encode (pairs.map (fun pair => pair.1+pair.2))
  have prepared := prepareInput_executes (pairs.map Prod.fst) (pairs.map Prod.snd)
  obtain ⟨addTime,addBound,added⟩ := add_executes_polynomial pairs [] []
  simp only [List.append_nil,List.length_nil,Nat.add_zero] at added addBound
  have moved := move_executes 33 2 1 7 (by decide) (by decide) (by decide)
    (file [] [] result [] [] [] [] [] [] [] []) rfl
  have movedStore : Function.update (Function.update (file [] [] result [] [] [] [] [] [] [] []) 1 (result++[])) 2 [] =
      file [] result [] [] [] [] [] [] [] [] [] := by
    funext r; fin_cases r <;> simp [file]
  change Executes _ _ (6*result.length+4)
    (Function.update (Function.update (file [] [] result [] [] [] [] [] [] [] []) 1 (result++[])) 2 []) at moved
  rw [movedStore] at moved
  obtain ⟨middle,middleRun,_,middleStore⟩ := prepared.sequence added
  have startMiddle : initial (sequence prepareInput addRoutine).program input = ⟨0,file input [] [] [] [] [] [] [] [] [] []⟩ := by
    apply congrArg (Config.mk _)
    funext r; fin_cases r <;> simp [file]
  have dataBound := run_dataLength (initial (sequence prepareInput addRoutine).program input) middle
    (6*input.length+5*first.length+6*second.length+12+1+addTime) (by rw [startMiddle]; exact middleRun)
  rw [initial_dataLength] at dataBound
  have outputBound : result.length ≤ middle.dataLength := by
    have entry := Finset.single_le_sum (f := fun register => (middle.store register).length)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ (2 : Register (sequence prepareInput addRoutine).program))
    have outputEntry : middle.store 2 = result := by
      rw [middleStore]
      simp [file,result]
    rw [← outputEntry]
    exact entry
  obtain ⟨last,ran,halted,stored⟩ := prepared.sequence (added.sequence moved)
  refine ⟨6*input.length+5*first.length+6*second.length+12+1+(addTime+1+(6*result.length+4)),last,?_,⟨?_,halted⟩,?_⟩
  · have inputLength : input.length = 2*first.length+1+second.length := by
      change (Encoding.frame first++second).length = _
      rw [List.length_append,Encoding.frame_length]
    have power := Nat.pow_le_pow_left (show first.length+second.length+1 ≤ input.length+1 by omega) 4
    change addTime ≤ 1000000000*(first.length+second.length+1)^4 at addBound
    have linear : input.length+1 ≤ (input.length+1)^4 := by
      have cube := Nat.one_le_pow' 3 input.length
      have product := Nat.mul_le_mul_left (input.length+1) cube
      nlinarith
    change _ ≤ 10000000000*(input.length+1)^4
    omega
  · have start : initial complete.program input = ⟨0,file input [] [] [] [] [] [] [] [] [] []⟩ := by
      apply congrArg (Config.mk _)
      funext r; fin_cases r <;> simp [file]
    rw [start]
    exact ran
  · rw [stored]
    simp [file,result]

end Counting.StackMachine.RowAdd
