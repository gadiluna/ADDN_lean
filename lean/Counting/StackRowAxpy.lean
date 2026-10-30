import Counting.StackRowAddBounds
import Counting.StackRowScaleBounds

namespace Counting.StackMachine.RowAxpy
open Routine

/-- Scalar, target row, source row, result; all remaining registers are private. -/
def file (factor target source result : List Bool) : Fin 37 → List Bool :=
  ![factor,target,source,result,[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
def scaleRoles : Fin 32 ↪ Fin 37 :=
  ⟨![0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32],by decide⟩
def addRoles : Fin 36 ↪ Fin 37 := ⟨fun r => ⟨r.val+1,by omega⟩,
  by intro a b equal; apply Fin.ext; have := congrArg (fun r : Fin 37 => r.val) equal; dsimp at this; omega⟩
abbrev scaleSource : Routine 35 := relocate RowScale.scaleRoutine scaleRoles
abbrev addRows : Routine 35 := relocate RowAdd.addRoutine addRoles
abbrev axpyRoutine : Routine 35 := sequence scaleSource (sequence (move 34 3 2 4) addRows)

theorem scaleSource_executes (factor : Rat) (target : List Bool) (source : List Rat) :
    ∃ time ≤ 300000000*((Encoding.rational.encode factor).length+(Encoding.rationalRow.encode source).length+1)^4,
      Executes scaleSource (file (Encoding.rational.encode factor) target (Encoding.rationalRow.encode source) []) time
        (file (Encoding.rational.encode factor) target [] (Encoding.rationalRow.encode (source.map (factor*·)))) := by
  obtain ⟨time,bounded,ran⟩ := RowScale.scale_executes_polynomial factor source []
  simp only [List.append_nil,List.length_nil,Nat.add_zero] at ran bounded
  refine ⟨time,bounded,?_⟩
  apply relocate_executes_frame RowScale.scaleRoutine scaleRoles _ _ _ _ time _ _ _ ran
  · funext r; fin_cases r <;> simp [file,RowScale.file,scaleRoles]
  · intro r; fin_cases r <;> simp [file,RowScale.file,scaleRoles]
  · intro r outside
    fin_cases r
    · simp [file]
    · simp [file]
    · exact False.elim (outside 1 rfl)
    · exact False.elim (outside 2 rfl)
    all_goals simp [file]

theorem addRows_executes (factor : List Bool) (pairs : List (Rat×Rat)) :
    ∃ time ≤ 1000000000*((Encoding.rationalRow.encode (pairs.map Prod.fst)).length+
      (Encoding.rationalRow.encode (pairs.map Prod.snd)).length+1)^4,
      Executes addRows (file factor (Encoding.rationalRow.encode (pairs.map Prod.fst))
        (Encoding.rationalRow.encode (pairs.map Prod.snd)) []) time
        (file factor [] [] (Encoding.rationalRow.encode (pairs.map (fun pair => pair.1+pair.2)))) := by
  obtain ⟨time,bounded,ran⟩ := RowAdd.add_executes_polynomial pairs [] []
  simp only [List.append_nil,List.length_nil,Nat.add_zero] at ran bounded
  refine ⟨time,bounded,?_⟩
  apply relocate_executes_frame RowAdd.addRoutine addRoles _ _ _ _ time _ _ _ ran
  · funext r; fin_cases r <;> simp [file,RowAdd.file,addRoles]
  · intro r; fin_cases r <;> simp [file,RowAdd.file,addRoles]
  · intro r outside
    fin_cases r
    · simp [file]
    · exact False.elim (outside 0 rfl)
    · exact False.elim (outside 1 rfl)
    · exact False.elim (outside 2 rfl)
    all_goals simp [file]

/-- Actual Gaussian row addition: scale the source, then add both encoded
coefficient streams. The source is consumed; a caller retaining the matrix
must explicitly copy or replace its row storage. -/
theorem axpy_executes (factor : Rat) (pairs : List (Rat×Rat)) :
    ∃ time ≤ 300000000*((Encoding.rational.encode factor).length+
      (Encoding.rationalRow.encode (pairs.map Prod.snd)).length+1)^4+
      6*(Encoding.rationalRow.encode (pairs.map (fun pair => factor*pair.2))).length+6+
      1000000000*((Encoding.rationalRow.encode (pairs.map Prod.fst)).length+
        (Encoding.rationalRow.encode (pairs.map (fun pair => factor*pair.2))).length+1)^4,
      Executes axpyRoutine (file (Encoding.rational.encode factor)
        (Encoding.rationalRow.encode (pairs.map Prod.fst)) (Encoding.rationalRow.encode (pairs.map Prod.snd)) []) time
        (file (Encoding.rational.encode factor) [] []
          (Encoding.rationalRow.encode (pairs.map (fun pair => pair.1+factor*pair.2)))) := by
  let scaled := Encoding.rationalRow.encode (pairs.map (fun pair => factor*pair.2))
  have sameScale : (pairs.map Prod.snd).map (factor*·) = pairs.map (fun pair => factor*pair.2) := by
    simp [List.map_map,Function.comp_def]
  obtain ⟨scaleTime,scaleBound,scaledRun⟩ := scaleSource_executes factor
    (Encoding.rationalRow.encode (pairs.map Prod.fst)) (pairs.map Prod.snd)
  rw [sameScale] at scaledRun
  have moved := move_executes 34 3 2 4 (by decide) (by decide) (by decide)
    (file (Encoding.rational.encode factor) (Encoding.rationalRow.encode (pairs.map Prod.fst)) [] scaled) rfl
  have movedStore : Function.update (Function.update (file (Encoding.rational.encode factor)
      (Encoding.rationalRow.encode (pairs.map Prod.fst)) [] scaled) 2 (scaled++[])) 3 [] =
      file (Encoding.rational.encode factor) (Encoding.rationalRow.encode (pairs.map Prod.fst)) scaled [] := by
    funext r; fin_cases r <;> simp [file]
  change Executes _ _ (6*scaled.length+4)
    (Function.update (Function.update (file (Encoding.rational.encode factor)
      (Encoding.rationalRow.encode (pairs.map Prod.fst)) [] scaled) 2 (scaled++[])) 3 []) at moved
  rw [movedStore] at moved
  obtain ⟨addTime,addBound,added⟩ := addRows_executes (Encoding.rational.encode factor)
    (pairs.map (fun pair => (pair.1,factor*pair.2)))
  simp only [List.map_map,Function.comp_def] at added addBound
  refine ⟨_,?_,scaledRun.sequence (moved.sequence added)⟩
  change addTime ≤ 1000000000*((Encoding.rationalRow.encode (pairs.map Prod.fst)).length+scaled.length+1)^4 at addBound
  change scaleTime+1+(6*scaled.length+4+1+addTime) ≤
    300000000*((Encoding.rational.encode factor).length+(Encoding.rationalRow.encode (pairs.map Prod.snd)).length+1)^4+
      6*scaled.length+6+1000000000*((Encoding.rationalRow.encode (pairs.map Prod.fst)).length+scaled.length+1)^4
  omega

end Counting.StackMachine.RowAxpy
