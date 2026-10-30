import Counting.StackMatrixColumn
import Counting.StackRowDotBounds

namespace Counting.StackMachine.GaussianNormal
open Routine RowAdd
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- Shared scalar work bank followed by immutable source matrix and row
count, two unary column indices, two column buffers, result, and scratch. -/
def bank (workspace : Fin 36 → List Bool) (matrix count first second left right result : List Bool) : Fin 44 → List Bool :=
  fun r => if small : r.val<36 then workspace ⟨r.val,small⟩
    else if r=36 then matrix else if r=37 then count else if r=38 then first else if r=39 then second
    else if r=40 then left else if r=41 then right else if r=42 then result else []
def ready (matrix count first second left right result : List Bool) : Fin 44 → List Bool :=
  bank (fun _ => []) matrix count first second left right result

def firstRoles : Fin 16 ↪ Fin 44 := ⟨![0,40,2,3,4,5,6,7,8,9,10,11,12,36,38,37],by decide⟩
def secondRoles : Fin 16 ↪ Fin 44 := ⟨![0,41,2,3,4,5,6,7,8,9,10,11,12,36,39,37],by decide⟩
def dotRoles : Fin 36 ↪ Fin 44 := ⟨fun r => ⟨r.val,by omega⟩,
  by intro a b equal;apply Fin.ext;exact congrArg (fun r : Fin 44 => r.val) equal⟩
abbrev readFirst : Routine 42 := relocate MatrixColumn.readColumn firstRoles
abbrev readSecond : Routine 42 := relocate MatrixColumn.readColumn secondRoles
abbrev compute : Routine 42 := sequence (move 41 40 0 43) (sequence (move 41 41 1 43)
  (sequence (relocate RowDot.dotRoutine dotRoles) (move 41 2 42 43)))
abbrev entry : Routine 42 := sequence readFirst (sequence readSecond compute)

theorem readFirst_executes (rows : List (List Rat)) (values : List Rat) (column : Nat)
    (selected : List.Forall₂ (fun row value => row[column]?=some value) rows values) (otherIndex : List Bool) :
    ∃ time ≤ 2020*((Encoding.rationalMatrix.encode rows).length+column+2)^2,
      Executes readFirst
        (ready (Encoding.rationalMatrix.encode rows) (List.replicate rows.length true) (List.replicate (column+1) true) otherIndex [] [] []) time
        (ready (Encoding.rationalMatrix.encode rows) (List.replicate rows.length true) (List.replicate (column+1) true) otherIndex (Encoding.rationalRow.encode values) [] []) := by
  obtain ⟨time,bounded,ran⟩ := MatrixColumn.readColumn_executes rows values column selected
  refine ⟨time,bounded,?_⟩
  apply relocate_executes_frame MatrixColumn.readColumn firstRoles _ _ _ _ time _ _ _ ran
  · funext r;fin_cases r <;> simp [ready,bank,firstRoles,MatrixColumn.file]
  · intro r;fin_cases r <;> simp [ready,bank,firstRoles,MatrixColumn.file]
  · intro r outside
    by_cases same : r=40
    · subst r;exact False.elim (outside 1 rfl)
    · simp [ready,bank,same]

theorem readSecond_executes (rows : List (List Rat)) (values : List Rat) (column : Nat)
    (selected : List.Forall₂ (fun row value => row[column]?=some value) rows values) (otherIndex left : List Bool) :
    ∃ time ≤ 2020*((Encoding.rationalMatrix.encode rows).length+column+2)^2,
      Executes readSecond
        (ready (Encoding.rationalMatrix.encode rows) (List.replicate rows.length true) otherIndex (List.replicate (column+1) true) left [] []) time
        (ready (Encoding.rationalMatrix.encode rows) (List.replicate rows.length true) otherIndex (List.replicate (column+1) true) left (Encoding.rationalRow.encode values) []) := by
  obtain ⟨time,bounded,ran⟩ := MatrixColumn.readColumn_executes rows values column selected
  refine ⟨time,bounded,?_⟩
  apply relocate_executes_frame MatrixColumn.readColumn secondRoles _ _ _ _ time _ _ _ ran
  · funext r;fin_cases r <;> simp [ready,bank,secondRoles,MatrixColumn.file]
  · intro r;fin_cases r <;> simp [ready,bank,secondRoles,MatrixColumn.file]
  · intro r outside
    by_cases same : r=41
    · subst r;exact False.elim (outside 1 rfl)
    · simp [ready,bank,same]

theorem compute_executes (pairs : List (Rat×Rat)) (matrix count first second : List Bool) :
    ∃ time ≤ 10000000000000*((Encoding.rationalRow.encode (pairs.map Prod.fst)).length+
        (Encoding.rationalRow.encode (pairs.map Prod.snd)).length+1)^4+
      6*(Encoding.rationalRow.encode (pairs.map Prod.fst)).length+
      6*(Encoding.rationalRow.encode (pairs.map Prod.snd)).length+
      6*(Encoding.rational.encode ((pairs.map (fun pair => pair.1*pair.2)).sum)).length+15,
      Executes compute
        (ready matrix count first second (Encoding.rationalRow.encode (pairs.map Prod.fst))
          (Encoding.rationalRow.encode (pairs.map Prod.snd)) []) time
        (ready matrix count first second [] [] (Encoding.rational.encode ((pairs.map (fun pair => pair.1*pair.2)).sum))) := by
  let left := Encoding.rationalRow.encode (pairs.map Prod.fst)
  let right := Encoding.rationalRow.encode (pairs.map Prod.snd)
  let result := Encoding.rational.encode ((pairs.map (fun pair => pair.1*pair.2)).sum)
  let initial := ready matrix count first second left right []
  let firstStore := bank (file left [] [] [] [] [] [] [] [] [] []) matrix count first second [] right []
  let secondStore := bank (file left right [] [] [] [] [] [] [] [] []) matrix count first second [] [] []
  let thirdStore := bank (file [] [] result [] [] [] [] [] [] [] []) matrix count first second [] [] []
  have a := move_executes 41 (40 : Fin 44) 0 43 (by decide) (by decide) (by decide) initial rfl
  have aStore : Function.update (Function.update initial 0 (left++[])) 40 []=firstStore := by
    funext r;fin_cases r <;> simp [initial,firstStore,ready,bank,file]
  change Executes _ initial (6*left.length+4) (Function.update (Function.update initial 0 (left++[])) 40 []) at a
  rw [aStore] at a
  have b := move_executes 41 (41 : Fin 44) 1 43 (by decide) (by decide) (by decide) firstStore rfl
  have bStore : Function.update (Function.update firstStore 1 (right++[])) 41 []=secondStore := by
    funext r;fin_cases r <;> simp [firstStore,secondStore,bank,file]
  change Executes _ firstStore (6*right.length+4) (Function.update (Function.update firstStore 1 (right++[])) 41 []) at b
  rw [bStore] at b
  obtain ⟨dotTime,dotBound,dotted⟩ := RowDot.dot_executes_polynomial pairs [] []
  simp only [List.append_nil,List.length_nil,Nat.add_zero] at dotted dotBound
  have c : Executes (relocate RowDot.dotRoutine dotRoles) secondStore dotTime thirdStore := by
    apply relocate_executes_frame RowDot.dotRoutine dotRoles _ _ _ _ dotTime _ _ _ dotted
    · funext r;fin_cases r <;> simp [secondStore,bank,file,dotRoles,left,right]
    · intro r;fin_cases r <;> simp [thirdStore,bank,file,dotRoles,result]
    · intro r outside
      have large : 36≤r.val := by
        by_contra bad
        exact outside ⟨r.val,by omega⟩ (Fin.ext rfl)
      simp [secondStore,thirdStore,bank,show ¬r.val<36 by omega]
  have d := move_executes 41 (2 : Fin 44) 42 43 (by decide) (by decide) (by decide) thirdStore rfl
  have dStore : Function.update (Function.update thirdStore 42 (result++[])) 2 []=
      ready matrix count first second [] [] result := by
    funext r;fin_cases r <;> simp [thirdStore,ready,bank,file]
  change Executes _ thirdStore (6*result.length+4) (Function.update (Function.update thirdStore 42 (result++[])) 2 []) at d
  rw [dStore] at d
  refine ⟨_,?_,a.sequence (b.sequence (c.sequence d))⟩
  dsimp only [left,right,result]
  omega

/-- One Gram-matrix entry, including both physical column copies and the
complete rational dot-product program. The original matrix and counters
remain available for the next entry. -/
theorem entry_executes (rows : List (List Rat)) (left right : List Rat) (first second : Nat)
    (leftSelected : List.Forall₂ (fun row value => row[first]?=some value) rows left)
    (rightSelected : List.Forall₂ (fun row value => row[second]?=some value) rows right) :
    ∃ time ≤ 200000000000000*((Encoding.rationalMatrix.encode rows).length+first+second+3)^4,
      Executes entry
        (ready (Encoding.rationalMatrix.encode rows) (List.replicate rows.length true)
          (List.replicate (first+1) true) (List.replicate (second+1) true) [] [] []) time
        (ready (Encoding.rationalMatrix.encode rows) (List.replicate rows.length true)
          (List.replicate (first+1) true) (List.replicate (second+1) true) [] []
          (Encoding.rational.encode ((List.zipWith (·*·) left right).sum))) := by
  let size := (Encoding.rationalMatrix.encode rows).length
  let total := size+first+second+3
  have equal : left.length=right.length := leftSelected.length_eq.symm.trans rightSelected.length_eq
  have paired : (left.zip right).map (fun pair => pair.1*pair.2)=List.zipWith (·*·) left right := by
    rw [List.map_zip_eq_zipWith]
    rfl
  obtain ⟨leftTime,leftBound,a⟩ := readFirst_executes rows left first leftSelected (List.replicate (second+1) true)
  obtain ⟨rightTime,rightBound,b⟩ := readSecond_executes rows right second rightSelected
    (List.replicate (first+1) true) (Encoding.rationalRow.encode left)
  obtain ⟨dotTime,dotBound,c⟩ := compute_executes (left.zip right) (Encoding.rationalMatrix.encode rows)
    (List.replicate rows.length true) (List.replicate (first+1) true) (List.replicate (second+1) true)
  simp only [List.map_fst_zip equal.le,List.map_snd_zip equal.ge,paired] at dotBound c
  refine ⟨_,?_,a.sequence (b.sequence c)⟩
  have leftSize := MatrixColumn.column_length_le rows left first leftSelected
  have rightSize := MatrixColumn.column_length_le rows right second rightSelected
  have resultSize := RowDot.result_length_le_rows (left.zip right)
  simp only [List.map_fst_zip equal.le,List.map_snd_zip equal.ge,paired] at resultSize
  have leftPower := Nat.pow_le_pow_left (show size+first+2 ≤ total by omega) 2
  have rightPower := Nat.pow_le_pow_left (show size+second+2 ≤ total by omega) 2
  have dotPower := Nat.pow_le_pow_left (show (Encoding.rationalRow.encode left).length+
    (Encoding.rationalRow.encode right).length+1 ≤ 2*total by omega) 4
  have squares : total^2 ≤ total^4 := Nat.pow_le_pow_right (by omega) (by decide : 2≤4)
  have linear : total ≤ total^4 := Nat.le_self_pow (by decide : 4≠0) total
  change leftTime ≤ 2020*(size+first+2)^2 at leftBound
  change rightTime ≤ 2020*(size+second+2)^2 at rightBound
  have sizeBound : size≤total := by omega
  change (Encoding.rationalRow.encode left).length ≤ size at leftSize
  change (Encoding.rationalRow.encode right).length ≤ size at rightSize
  have scaledPower : ((Encoding.rationalRow.encode left).length+(Encoding.rationalRow.encode right).length+1)^4 ≤ 16*total^4 := by
    nlinarith [dotPower]
  have positive : 1≤total^4 := Nat.one_le_pow 4 total (by omega)
  change _ ≤ 200000000000000*total^4
  omega

end Counting.StackMachine.GaussianNormal
