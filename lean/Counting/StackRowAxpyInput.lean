import Counting.StackRowAxpyBounds

namespace Counting.StackMachine.RowAxpy
open Routine EncodingPrograms

def inputCodec : Encoding.Codec (Rat×(List Rat×List Rat)) :=
  Encoding.product (Encoding.framed Encoding.rational)
    (Encoding.product (Encoding.framed Encoding.rationalRow) Encoding.rationalRow)
abbrev prepareInput : Routine 35 := sequence (move 34 0 4 7)
  (sequence (ofProgram (unframeProgram 34 4 0 7))
    (sequence (ofProgram (unframeProgram 34 4 1 7)) (move 34 4 2 7)))
abbrev complete : Routine 35 := sequence prepareInput (sequence axpyRoutine (move 34 3 1 4))
def completeCost : Nat := 10*costConstant+1000

theorem prepareInput_executes (factor : Rat) (target source : List Rat) :
    Executes prepareInput (file (inputCodec.encode (factor,(target,source))) [] [] [])
      (6*(inputCodec.encode (factor,(target,source))).length+5*(Encoding.rational.encode factor).length+
        5*(Encoding.rationalRow.encode target).length+6*(Encoding.rationalRow.encode source).length+15)
      (file (Encoding.rational.encode factor) (Encoding.rationalRow.encode target) (Encoding.rationalRow.encode source) []) := by
  let input := inputCodec.encode (factor,(target,source))
  let F := Encoding.rational.encode factor
  let T := Encoding.rationalRow.encode target
  let S := Encoding.rationalRow.encode source
  let rest := Encoding.frame T++S
  have moved := move_executes 34 0 4 7 (by decide) (by decide) (by decide) (file input [] [] []) rfl
  have movedStore : Function.update (Function.update (file input [] [] []) 4 (input++[])) 0 [] =
      Function.update (file [] [] [] []) 4 input := by
    funext r; fin_cases r <;> simp [file]
  change Executes _ _ (6*input.length+4)
    (Function.update (Function.update (file input [] [] []) 4 (input++[])) 0 []) at moved
  rw [movedStore] at moved
  let base := Function.update (file [] [] [] []) 4 input
  have start : unframeConfig 34 4 0 7 0 base (Encoding.frame F++rest) [] [] =
      (⟨0,base⟩ : Config (unframeProgram 34 4 0 7)) := by
    apply congrArg (Config.mk _)
    change (fun r : Fin 37 => _) = base
    funext r; fin_cases r <;> simp [base,input,F,T,S,rest,inputCodec,Encoding.product,Encoding.framed,file]
  have ran := unframe_frames 34 4 0 7 (by decide) (by decide) (by decide) base F rest []
  rw [start] at ran
  have parsedFactor : Executes (ofProgram (unframeProgram 34 4 0 7)) base (5*F.length+2)
      (Function.update (file F [] [] []) 4 rest) := by
    refine ⟨unframeConfig 34 4 0 7 7 base rest (F++[]) [],ran,(unframe_halted _ _ _ _ _ _ _ _).1,?_⟩
    change (fun r : Fin 37 => _) = _
    funext r; fin_cases r <;> simp [unframeConfig,base,file,Function.update]
  let middle := Function.update (file F [] [] []) 4 rest
  have middleStart : unframeConfig 34 4 1 7 0 middle (Encoding.frame T++S) [] [] =
      (⟨0,middle⟩ : Config (unframeProgram 34 4 1 7)) := by
    apply congrArg (Config.mk _)
    change (fun r : Fin 37 => _) = middle
    funext r; fin_cases r <;> simp [middle,rest,file]
  have ranTarget := unframe_frames 34 4 1 7 (by decide) (by decide) (by decide) middle T S []
  rw [middleStart] at ranTarget
  have parsedTarget : Executes (ofProgram (unframeProgram 34 4 1 7)) middle (5*T.length+2)
      (Function.update (file F T [] []) 4 S) := by
    refine ⟨unframeConfig 34 4 1 7 7 middle S (T++[]) [],ranTarget,(unframe_halted _ _ _ _ _ _ _ _).1,?_⟩
    change (fun r : Fin 37 => _) = _
    funext r; fin_cases r <;> simp [unframeConfig,middle,file,Function.update]
  have delivered := move_executes 34 4 2 7 (by decide) (by decide) (by decide)
    (Function.update (file F T [] []) 4 S) (by simp [file])
  have deliveredStore : Function.update (Function.update (Function.update (file F T [] []) 4 S) 2 (S++[])) 4 [] =
      file F T S [] := by
    funext r; fin_cases r <;> simp [file]
  change Executes _ _ (6*S.length+4)
    (Function.update (Function.update (Function.update (file F T [] []) 4 S) 2 (S++[])) 4 []) at delivered
  rw [deliveredStore] at delivered
  have combined := moved.sequence (parsedFactor.sequence (parsedTarget.sequence delivered))
  change Executes prepareInput (file input [] [] [])
    (6*input.length+4+1+(5*F.length+2+1+(5*T.length+2+1+(6*S.length+4)))) (file F T S []) at combined
  convert combined using 1
  change 6*input.length+5*F.length+5*T.length+6*S.length+15 = _
  omega

theorem complete_halts (factor : Rat) (pairs : List (Rat×Rat)) :
    ∃ steps output,
      steps ≤ completeCost*((inputCodec.encode (factor,(pairs.map Prod.fst,pairs.map Prod.snd))).length+1)^16 ∧
      HaltsAt complete.program (inputCodec.encode (factor,(pairs.map Prod.fst,pairs.map Prod.snd))) steps output ∧
      output.store 1 = Encoding.rationalRow.encode (pairs.map (fun pair => pair.1+factor*pair.2)) := by
  let input := inputCodec.encode (factor,(pairs.map Prod.fst,pairs.map Prod.snd))
  let F := Encoding.rational.encode factor
  let T := Encoding.rationalRow.encode (pairs.map Prod.fst)
  let S := Encoding.rationalRow.encode (pairs.map Prod.snd)
  let result := Encoding.rationalRow.encode (pairs.map (fun pair => pair.1+factor*pair.2))
  have prepared := prepareInput_executes factor (pairs.map Prod.fst) (pairs.map Prod.snd)
  obtain ⟨coreTime,coreBound,coreRun⟩ := axpy_executes_polynomial factor pairs
  have moved := move_executes 34 3 1 4 (by decide) (by decide) (by decide) (file F [] [] result) rfl
  have movedStore : Function.update (Function.update (file F [] [] result) 1 (result++[])) 3 [] = file F result [] [] := by
    funext r; fin_cases r <;> simp [file]
  change Executes _ _ (6*result.length+4)
    (Function.update (Function.update (file F [] [] result) 1 (result++[])) 3 []) at moved
  rw [movedStore] at moved
  obtain ⟨middle,middleRun,_,middleStore⟩ := prepared.sequence coreRun
  have startMiddle : initial (sequence prepareInput axpyRoutine).program input = ⟨0,file input [] [] []⟩ := by
    apply congrArg (Config.mk _)
    funext r; fin_cases r <;> simp [file]
  have dataBound := run_dataLength (initial (sequence prepareInput axpyRoutine).program input) middle
    (6*input.length+5*F.length+5*T.length+6*S.length+15+1+coreTime) (by rw [startMiddle]; exact middleRun)
  rw [initial_dataLength] at dataBound
  have outputBound : result.length ≤ middle.dataLength := by
    have entry := Finset.single_le_sum (f := fun register => (middle.store register).length)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ (3 : Register (sequence prepareInput axpyRoutine).program))
    have outputEntry : middle.store 3 = result := by rw [middleStore]; simp [file,result]
    rw [← outputEntry]
    exact entry
  obtain ⟨last,ran,halted,stored⟩ := prepared.sequence (coreRun.sequence moved)
  refine ⟨6*input.length+5*F.length+5*T.length+6*S.length+15+1+(coreTime+1+(6*result.length+4)),last,?_,⟨?_,halted⟩,?_⟩
  · have inputLength : input.length = 2*F.length+1+(2*T.length+1+S.length) := by
      change (Encoding.frame F++(Encoding.frame T++S)).length = _
      simp only [List.length_append,Encoding.frame_length]
    have power := Nat.pow_le_pow_left (show F.length+T.length+S.length+1 ≤ input.length+1 by omega) 16
    change coreTime ≤ costConstant*(F.length+T.length+S.length+1)^16 at coreBound
    have coreInputBound := coreBound.trans (Nat.mul_le_mul_left costConstant power)
    have linear : input.length+1 ≤ (input.length+1)^16 := by
      exact Nat.le_self_pow (by decide) _
    change _ ≤ completeCost*(input.length+1)^16
    unfold completeCost
    unfold costConstant at coreInputBound ⊢
    omega
  · have start : initial complete.program input = ⟨0,file input [] [] []⟩ := by
      apply congrArg (Config.mk _)
      funext r; fin_cases r <;> simp [file]
    rw [start]
    exact ran
  · rw [stored]
    simp [file,result]

end Counting.StackMachine.RowAxpy
