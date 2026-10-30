import Counting.StackRowScaleBounds

namespace Counting.StackMachine.RowScale
open Routine EncodingPrograms

abbrev prepareInput : Routine 30 := sequence (move 29 0 1 7) (ofProgram (unframeProgram 29 1 0 7))
abbrev complete : Routine 30 := sequence prepareInput (sequence scaleRoutine (move 29 2 1 7))
def inputCodec : Encoding.Codec (Rat×List Rat) := Encoding.product (Encoding.framed Encoding.rational) Encoding.rationalRow

theorem prepareInput_executes (factor : Rat) (row : List Rat) :
    Executes prepareInput (file (inputCodec.encode (factor,row)) [] [] [] [] [] [] [] [])
      (6*(inputCodec.encode (factor,row)).length+5*(Encoding.rational.encode factor).length+7)
      (file (Encoding.rational.encode factor) (Encoding.rationalRow.encode row) [] [] [] [] [] [] []) := by
  let input := inputCodec.encode (factor,row)
  let scalar := Encoding.rational.encode factor
  let rowCode := Encoding.rationalRow.encode row
  have moved := move_executes 29 0 1 7 (by decide) (by decide) (by decide) (file input [] [] [] [] [] [] [] []) rfl
  have movedStore : Function.update (Function.update (file input [] [] [] [] [] [] [] []) 1 (input++[])) 0 [] =
      file [] input [] [] [] [] [] [] [] := by
    funext r; fin_cases r <;> simp [file]
  change Executes _ _ (6*input.length+4)
    (Function.update (Function.update (file input [] [] [] [] [] [] [] []) 1 (input++[])) 0 []) at moved
  rw [movedStore] at moved
  let base := file [] input [] [] [] [] [] [] []
  have start : unframeConfig 29 1 0 7 0 base (Encoding.frame scalar++rowCode) [] [] =
      (⟨0,base⟩ : Config (unframeProgram 29 1 0 7)) := by
    apply congrArg (Config.mk _)
    change (fun r : Fin 32 => _) = base
    funext r; fin_cases r <;> simp [base,input,scalar,rowCode,inputCodec,Encoding.product,Encoding.framed,file]
  have ran := unframe_frames 29 1 0 7 (by decide) (by decide) (by decide) base scalar rowCode []
  rw [start] at ran
  have parsedRun : Executes (ofProgram (unframeProgram 29 1 0 7)) base (5*scalar.length+2)
      (file scalar rowCode [] [] [] [] [] [] []) := by
    refine ⟨unframeConfig 29 1 0 7 7 base rowCode (scalar++[]) [],ran,(unframe_halted _ _ _ _ _ _ _ _).1,?_⟩
    change (fun r : Fin 32 => _) = _
    funext r; fin_cases r <;> simp [unframeConfig,base,file]
  convert moved.sequence parsedRun using 1
  change 6*input.length+5*scalar.length+7 = 6*input.length+4+1+(5*scalar.length+2)
  omega

theorem complete_halts (factor : Rat) (row : List Rat) :
    ∃ steps output,
      steps ≤ 3000000000*((inputCodec.encode (factor,row)).length+1)^4 ∧
      HaltsAt complete.program (inputCodec.encode (factor,row)) steps output ∧
      output.store 1 = Encoding.rationalRow.encode (row.map (factor*·)) := by
  let input := inputCodec.encode (factor,row)
  let factorCode := Encoding.rational.encode factor
  let rowCode := Encoding.rationalRow.encode row
  let resultCode := Encoding.rationalRow.encode (row.map (factor*·))
  have prepared := prepareInput_executes factor row
  obtain ⟨scaleTime,scaleBound,scaled⟩ := scale_executes_polynomial factor row []
  simp only [List.append_nil,List.length_nil,Nat.add_zero] at scaled scaleBound
  have moved := move_executes 29 2 1 7 (by decide) (by decide) (by decide)
    (file factorCode [] resultCode [] [] [] [] [] []) rfl
  have movedStore : Function.update (Function.update (file factorCode [] resultCode [] [] [] [] [] []) 1 (resultCode++[])) 2 [] =
      file factorCode resultCode [] [] [] [] [] [] [] := by
    funext r; fin_cases r <;> simp [file]
  change Executes _ _ (6*resultCode.length+4)
    (Function.update (Function.update (file factorCode [] resultCode [] [] [] [] [] []) 1 (resultCode++[])) 2 []) at moved
  rw [movedStore] at moved
  obtain ⟨middle,middleRun,_,middleStore⟩ := prepared.sequence scaled
  have startMiddle : initial (sequence prepareInput scaleRoutine).program input = ⟨0,file input [] [] [] [] [] [] [] []⟩ := by
    apply congrArg (Config.mk _)
    funext r; fin_cases r <;> simp [file]
  have dataBound := run_dataLength (initial (sequence prepareInput scaleRoutine).program input) middle
    (6*input.length+5*factorCode.length+7+1+scaleTime) (by rw [startMiddle]; exact middleRun)
  rw [initial_dataLength] at dataBound
  have outputBound : resultCode.length ≤ middle.dataLength := by
    have entry := Finset.single_le_sum (f := fun register => (middle.store register).length)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ (2 : Register (sequence prepareInput scaleRoutine).program))
    have outputEntry : middle.store 2 = resultCode := by
      rw [middleStore]
      simp [file,resultCode]
    rw [← outputEntry]
    exact entry
  obtain ⟨last,ran,halted,stored⟩ := prepared.sequence (scaled.sequence moved)
  refine ⟨6*input.length+5*factorCode.length+7+1+(scaleTime+1+(6*resultCode.length+4)),last,?_,⟨?_,halted⟩,?_⟩
  · have inputLength : input.length = 2*factorCode.length+1+rowCode.length := by
      change (Encoding.frame factorCode++rowCode).length = _
      rw [List.length_append,Encoding.frame_length]
    have factorBound : factorCode.length ≤ input.length := by omega
    have power := Nat.pow_le_pow_left (show factorCode.length+rowCode.length+1 ≤ input.length+1 by omega) 4
    change scaleTime ≤ 300000000*(factorCode.length+rowCode.length+1)^4 at scaleBound
    have linear : input.length+1 ≤ (input.length+1)^4 := by
      have cube := Nat.one_le_pow' 3 input.length
      have product := Nat.mul_le_mul_left (input.length+1) cube
      nlinarith
    change _ ≤ 3000000000*(input.length+1)^4
    omega
  · have start : initial complete.program input = ⟨0,file input [] [] [] [] [] [] [] []⟩ := by
      apply congrArg (Config.mk _)
      funext r; fin_cases r <;> simp [file]
    rw [start]
    exact ran
  · rw [stored]
    rfl

end Counting.StackMachine.RowScale
