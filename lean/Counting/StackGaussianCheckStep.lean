import Counting.StackRowDotBounds
import Counting.StackPositiveNaturalsCall
import Counting.StackRationalPredicateSpec
import Counting.StackBooleanFold
import Counting.StackUnframeCanonical

namespace Counting.StackMachine.GaussianCheck
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- The dot-product workspace occupies the first 36 registers. The
remaining registers retain the unread rows, common vector, countdown,
conjunction, and the two temporary cells used by the scalar call. -/
def file (left right value rows vector count status flag : List Bool) : Fin 43 → List Bool :=
  fun r => if h : r.val<36 then RowAdd.file left right value [] [] [] [] [] [] [] [] ⟨r.val,h⟩
    else if r=36 then rows else if r=37 then vector else if r=38 then count
    else if r=39 then status else if r=41 then flag else []

def dotRoles : Fin 36 ↪ Fin 43 := ⟨fun r => ⟨r.val,by omega⟩,
  by intro a b same;exact Fin.ext (congrArg (fun r:Fin 43=>r.val) same)⟩
def testRoles : Fin 20 ↪ Fin 43 :=
  ⟨![2,41,40,42,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18],by decide⟩
abbrev readRow : Routine 41 := ofProgram (unframeProgram 40 36 0 40)
abbrev copyVector : Routine 41 := ofProgram (ListPrograms.copyProgram 40 37 1 40)
abbrev dot : Routine 41 := relocate RowDot.dotRoutine dotRoles
abbrev testZero : Routine 41 := relocate
  (PositiveNaturalsCall.invoke (RationalArithmetic.Predicates.routine .zero)) testRoles
abbrev combine : Routine 41 := BooleanFold.single .conjunction 41 39
abbrev body : Routine 41 := sequence readRow (sequence copyVector
  (sequence dot (sequence testZero (sequence combine (clear 2)))))

theorem readRow_executes (row suffix vector count status : List Bool) :
    Executes readRow (file [] [] [] (Encoding.frame row++suffix) vector count status [])
      (5*row.length+2) (file row [] [] suffix vector count status []) := by
  let initial := file [] [] [] (Encoding.frame row++suffix) vector count status []
  have ran := unframe_canonical_executes 40 (36:Fin 43) 0 40 (by decide) (by decide) (by decide)
    initial row suffix rfl rfl
  have stored : Function.update (Function.update initial 36 suffix) 0 (row++[])=
      file row [] [] suffix vector count status [] := by
    funext r;fin_cases r <;> simp [initial,file,RowAdd.file]
  change Executes _ initial (5*row.length+2)
    (Function.update (Function.update initial 36 suffix) 0 (row++[])) at ran
  rw [stored] at ran
  exact ran

theorem copyVector_executes (row suffix vector count status : List Bool) :
    Executes copyVector (file row [] [] suffix vector count status [])
      (5*vector.length+2) (file row vector [] suffix vector count status []) := by
  let initial := file row [] [] suffix vector count status []
  have ran := copy_executes 40 (37:Fin 43) 1 40 (by decide) (by decide) (by decide) initial rfl
  have stored : Function.update initial 1 (vector++[])=file row vector [] suffix vector count status [] := by
    funext r;fin_cases r <;> simp [initial,file,RowAdd.file]
  change Executes _ initial (5*vector.length+2) (Function.update initial 1 (vector++[])) at ran
  rw [stored] at ran
  exact ran

theorem dot_executes (left right : List Rat) (same : left.length=right.length)
    (rows count status : List Bool) :
    ∃ time ≤ 10000000000000*((Encoding.rationalRow.encode left).length+
        (Encoding.rationalRow.encode right).length+1)^4,
      Executes dot (file (Encoding.rationalRow.encode left) (Encoding.rationalRow.encode right) [] rows
        (Encoding.rationalRow.encode right) count status []) time
        (file [] [] (Encoding.rational.encode ((List.zipWith (·*·) left right).sum)) rows
          (Encoding.rationalRow.encode right) count status []) := by
  let pairs := left.zip right
  have first : pairs.map Prod.fst=left := List.map_fst_zip (by omega)
  have second : pairs.map Prod.snd=right := List.map_snd_zip (by omega)
  obtain ⟨time,bounded,ran⟩ := RowDot.dot_executes_polynomial pairs [] []
  rw [first,second] at bounded ran
  simp only [List.length_nil,Nat.add_zero,List.append_nil] at bounded ran
  have product : pairs.map (fun pair => pair.1*pair.2)=List.zipWith (·*·) left right := by
    exact List.map_zip_eq_zipWith
  rw [product] at ran
  refine ⟨time,bounded,?_⟩
  apply relocate_executes_frame RowDot.dotRoutine dotRoles _ _ _ _ time _ _ _ ran
  · funext r;fin_cases r <;> simp [file,dotRoles]
  · intro r;fin_cases r <;> simp [file,dotRoles]
  · intro r outside
    fin_cases r
    all_goals first | exact False.elim (outside 0 rfl) | exact False.elim (outside 1 rfl) | exact False.elim (outside 2 rfl) | simp [file,RowAdd.file]

theorem testZero_executes (value : Rat) (rows vector count status : List Bool) :
    ∃ time ≤ 2000*((Encoding.rational.encode value).length+1),
      Executes testZero (file [] [] (Encoding.rational.encode value) rows vector count status []) time
        (file [] [] (Encoding.rational.encode value) rows vector count status [decide (value=0)]) := by
  obtain ⟨time,bounded,ran⟩ := PositiveNaturalsCall.invoke_executes
    (RationalArithmetic.Predicates.routine .zero) _ _
    (RationalArithmetic.Predicates.predicate_computes .zero) (Encoding.rational.encode value)
  change Executes _ _ time (PositiveNaturalsCall.file (Encoding.rational.encode value)
    [RationalArithmetic.Predicates.predicate .zero (Encoding.rational.encode value)] [] []) at ran
  rw [RationalArithmetic.Predicates.zero_correct] at ran
  refine ⟨time,bounded.trans (by simp only [Complexity.polynomial,pow_one];omega),?_⟩
  apply relocate_executes_frame _ testRoles _ _ _ _ time _ _ _ ran
  · funext r;fin_cases r <;> simp [file,RowAdd.file,testRoles,PositiveNaturalsCall.file]
  · intro r;fin_cases r <;> simp [file,RowAdd.file,testRoles,PositiveNaturalsCall.file]
  · intro r outside
    fin_cases r
    all_goals first | exact False.elim (outside 1 rfl) | simp [file,RowAdd.file]

theorem combine_executes (value rows vector count : List Bool) (accepted valid : Bool) :
    Executes combine (file [] [] value rows vector count [accepted] [valid]) 3
      (file [] [] value rows vector count [accepted && valid] []) := by
  have ran := BooleanFold.single_executes .conjunction (41:Fin 43) 39 (by decide)
    (file [] [] value rows vector count [accepted] [valid]) valid accepted [] [] rfl rfl
  have stored : BooleanFold.updated 41 39 (file [] [] value rows vector count [accepted] [valid]) []
      (BooleanFold.operation .conjunction accepted valid) []=
      file [] [] value rows vector count [accepted && valid] [] := by
    funext r;fin_cases r <;> simp [file,RowAdd.file,BooleanFold.updated,BooleanFold.operation]
  rw [stored] at ran
  exact ran

theorem clearValue_executes (value rows vector count status : List Bool) :
    Executes (clear (registers:=41) 2) (file [] [] value rows vector count status [])
      (value.length+1) (file [] [] [] rows vector count status []) := by
  have ran := clear_executes (registers:=41) 2 (file [] [] value rows vector count status [])
  have stored : Function.update (file [] [] value rows vector count status []) 2 []=
      file [] [] [] rows vector count status [] := by
    funext r;fin_cases r <;> simp [file,RowAdd.file]
  change Executes _ _ (value.length+1) _ at ran
  rw [stored] at ran
  exact ran

theorem body_executes (row vector : List Rat) (same : row.length=vector.length)
    (suffix count : List Bool) (accepted : Bool) :
    ∃ time ≤ 100000000000000*((Encoding.rationalRow.encode row).length+
        (Encoding.rationalRow.encode vector).length+1)^4,
      Executes body (file [] [] [] (Encoding.frame (Encoding.rationalRow.encode row)++suffix)
        (Encoding.rationalRow.encode vector) count [accepted] []) time
        (file [] [] [] suffix (Encoding.rationalRow.encode vector) count
          [accepted && decide ((List.zipWith (·*·) row vector).sum=0)] []) := by
  have a := readRow_executes (Encoding.rationalRow.encode row) suffix (Encoding.rationalRow.encode vector) count [accepted]
  have b := copyVector_executes (Encoding.rationalRow.encode row) suffix (Encoding.rationalRow.encode vector) count [accepted]
  obtain ⟨dotTime,dotBound,c⟩ := dot_executes row vector same suffix count [accepted]
  let value := (List.zipWith (·*·) row vector).sum
  obtain ⟨testTime,testBound,d⟩ := testZero_executes value suffix (Encoding.rationalRow.encode vector) count [accepted]
  have e := combine_executes (Encoding.rational.encode value) suffix (Encoding.rationalRow.encode vector) count accepted (decide (value=0))
  have f := clearValue_executes (Encoding.rational.encode value) suffix (Encoding.rationalRow.encode vector) count [accepted && decide (value=0)]
  have valueBound := RowDot.result_length_le_rows (row.zip vector)
  rw [List.map_fst_zip (by omega),List.map_snd_zip (by omega)] at valueBound
  have product : (row.zip vector).map (fun pair => pair.1*pair.2)=List.zipWith (·*·) row vector := by
    exact List.map_zip_eq_zipWith
  rw [product] at valueBound
  have linear := Nat.le_self_pow (by decide : 4≠0)
    ((Encoding.rationalRow.encode row).length+(Encoding.rationalRow.encode vector).length+1)
  refine ⟨_,?_,a.sequence (b.sequence (c.sequence (d.sequence (e.sequence f))))⟩
  dsimp only [value] at *
  omega

end Counting.StackMachine.GaussianCheck
