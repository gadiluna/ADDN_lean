import Counting.StackGaussianCheckInput
import Counting.StackMatrixSwapBounds

namespace Counting.StackMachine.GaussianCheck
open Routine GaussianEquationCheck
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

abbrev finish : Routine 41 := sequence (clear 37) (move 40 39 1 40)
abbrev complete : Routine 41 := sequence prepare (sequence loop finish)

theorem finish_executes (vector : List Bool) (accepted : Bool) :
    Executes finish (file [] [] [] [] vector [] [accepted] []) (vector.length+12)
      (file [] [accepted] [] [] [] [] [] []) := by
  have a := clear_executes (registers:=41) 37 (file [] [] [] [] vector [] [accepted] [])
  have cleared : Function.update (file [] [] [] [] vector [] [accepted] []) 37 []=
      file [] [] [] [] [] [] [accepted] [] := by
    funext r;fin_cases r <;> simp [file,RowAdd.file]
  change Executes _ _ (vector.length+1) _ at a
  rw [cleared] at a
  have b := move_executes 40 (39:Fin 43) 1 40 (by decide) (by decide) (by decide)
    (file [] [] [] [] [] [] [accepted] []) rfl
  have delivered : Function.update (Function.update (file [] [] [] [] [] [] [accepted] []) 1 ([accepted]++[])) 39 []=
      file [] [accepted] [] [] [] [] [] [] := by
    funext r;fin_cases r <;> simp [file,RowAdd.file]
  change Executes _ _ 10
    (Function.update (Function.update (file [] [] [] [] [] [] [accepted] []) 1 ([accepted]++[])) 39 []) at b
  rw [delivered] at b
  convert a.sequence b using 1

/-- Polynomial bound for the concrete row checker. The length condition
is explicit; malformed inputs and unequal row widths are outside this
canonical internal interface. -/
theorem complete_executes (rows : List (List Rat)) (solution : List Rat)
    (same : ∀ row∈rows,row.length=solution.length) :
    ∃ time ≤ 1000000000000000*((inputCodec.encode (solution,rows)).length+1)^5,
      Executes complete (file (inputCodec.encode (solution,rows)) [] [] [] [] [] [] []) time
        (file [] [accepts rows solution] [] [] [] [] [] []) := by
  obtain ⟨prepareTime,prepareBound,a⟩ := prepare_executes rows solution
  obtain ⟨loopTime,loopBound,b⟩ := loop_executes rows solution
    (Encoding.rationalMatrix.encode rows).length same
    (fun row member=>Encoding.framedList_member_length_le Encoding.rationalRow rows row member) [] true
  simp only [List.append_nil,Bool.true_and] at b
  have c := finish_executes (Encoding.rationalRow.encode solution) (accepts rows solution)
  refine ⟨_,?_,a.sequence (b.sequence c)⟩
  let size := (inputCodec.encode (solution,rows)).length
  have length : size=2*(Encoding.rationalRow.encode solution).length+1+
      (Encoding.rationalMatrix.encode rows).length := by
    change (Encoding.frame (Encoding.rationalRow.encode solution)++Encoding.rationalMatrix.encode rows).length=_
    simp [Encoding.frame_length]
  have count := Encoding.framedList_count_le Encoding.rationalRow rows
  change rows.length≤ (Encoding.rationalMatrix.encode rows).length at count
  have bodyPower := Nat.pow_le_pow_left
    (show (Encoding.rationalMatrix.encode rows).length+(Encoding.rationalRow.encode solution).length+1≤ size+1 by omega) 4
  have charged := Nat.mul_le_mul_left rows.length (Nat.mul_le_mul_left 100000000000000 bodyPower)
  have countPower := Nat.mul_le_mul_right (100000000000000*(size+1)^4)
    (show rows.length≤ size+1 by omega)
  have loopLimit : loopTime≤ 100000000000000*(size+1)^5+2*(size+1)+1 := by
    dsimp only [rowBudget] at loopBound
    have sameProduct : (size+1)*(100000000000000*(size+1)^4)=100000000000000*(size+1)^5 := by ring
    rw [sameProduct] at countPower
    nlinarith
  have cube : (size+1)^3≤ (size+1)^5 := Nat.pow_le_pow_right (by omega) (by omega)
  have linear := Nat.le_self_pow (by decide:5≠0) (size+1)
  change prepareTime≤ 1900*(size+1)^3 at prepareBound
  change _≤ 1000000000000000*(size+1)^5
  omega

theorem complete_halts (rows : List (List Rat)) (solution : List Rat)
    (same : ∀ row∈rows,row.length=solution.length) :
    ∃ time output,
      time≤ 1000000000000000*((inputCodec.encode (solution,rows)).length+1)^5 ∧
      HaltsAt complete.program (inputCodec.encode (solution,rows)) time output ∧
      output.store 1=[accepts rows solution] := by
  obtain ⟨time,bounded,output,ran,halted,stored⟩ := complete_executes rows solution same
  refine ⟨time,output,bounded,⟨?_,halted⟩,?_⟩
  · have initialStore : initial complete.program (inputCodec.encode (solution,rows))=
        ⟨0,file (inputCodec.encode (solution,rows)) [] [] [] [] [] [] []⟩ := by
      apply congrArg (Config.mk _)
      funext r;fin_cases r <;> simp [file,RowAdd.file]
    rw [initialStore]
    exact ran
  · rw [stored]
    rfl

end Counting.StackMachine.GaussianCheck
