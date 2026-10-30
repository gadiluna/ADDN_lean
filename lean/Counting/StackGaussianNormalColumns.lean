import Counting.StackGaussianNormalEmit
import Counting.GaussianNormalMatrix

namespace Counting.StackMachine.GaussianNormal
open Routine GaussianNormalMatrix
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

def outerBank (workspace : Fin 44 → List Bool) (width columns rows rowRev matrixRev rowHeader matrixHeader : List Bool) :
    Fin 53 → List Bool :=
  fun r => if small : r.val<44 then workspace ⟨r.val,small⟩
    else if r=44 then width else if r=45 then columns else if r=46 then rows
    else if r=47 then rowRev else if r=48 then matrixRev else if r=49 then rowHeader
    else if r=50 then matrixHeader else []

def entryRoles : Fin 44 ↪ Fin 53 := ⟨fun r => ⟨r.val,by omega⟩,
  by intro a b equal;apply Fin.ext;exact congrArg (fun r : Fin 53 => r.val) equal⟩

def state (width : Nat) (equations : List Executable.Equation) (first second : Nat)
    (columns rows rowRev matrixRev result : List Bool) : Fin 53 → List Bool :=
  outerBank (ready (Encoding.rationalMatrix.encode (equationMatrix width equations))
    (List.replicate equations.length true) (List.replicate (first+1) true) (List.replicate (second+1) true) [] [] result)
    (List.replicate width true) columns rows rowRev matrixRev
    (Encoding.natural.encode (width+1)) (Encoding.natural.encode width)

def cell (width : Nat) (equations : List Executable.Equation) (first second : Nat) : Rat :=
  dot (column (equationMatrix width equations) first) (column (equationMatrix width equations) second)

abbrev localEntry : Routine 51 := relocate entry entryRoles
abbrev columnBody : Routine 51 := sequence localEntry (sequence emitScalar (pushBit 39 true))
abbrev columnLoop : Routine 51 := forEach 45 columnBody

def columnBudget (size width : Nat) : Nat := 200000000000000*(size+2*width+3)^4+100*(size+1)

theorem localEntry_executes (width : Nat) (equations : List Executable.Equation) (first second : Nat)
    (firstBound : first<width) (secondBound : second<width+1) (columns rows rowRev matrixRev : List Bool) :
    ∃ time ≤ 200000000000000*((Encoding.rationalMatrix.encode (equationMatrix width equations)).length+first+second+3)^4,
      Executes localEntry (state width equations first second columns rows rowRev matrixRev []) time
        (state width equations first second columns rows rowRev matrixRev
          (Encoding.rational.encode (cell width equations first second))) := by
  obtain ⟨time,bounded,ran⟩ := entry_executes (equationMatrix width equations)
    (column (equationMatrix width equations) first) (column (equationMatrix width equations) second) first second
    (equationMatrix_column_selected width equations ⟨first,by omega⟩)
    (equationMatrix_column_selected width equations ⟨second,secondBound⟩)
  refine ⟨time,bounded,?_⟩
  apply relocate_executes_frame entry entryRoles _ _ _ _ time _ _ _ ran
  · funext r;fin_cases r <;> simp [state,outerBank,entryRoles]
  · intro r;fin_cases r <;> simp [state,outerBank,entryRoles,cell,dot]
  · intro r outside
    have large : 44≤r.val := by
      by_contra bad
      exact outside ⟨r.val,by omega⟩ (Fin.ext rfl)
    simp [state,outerBank,show ¬r.val<44 by omega]

theorem cell_length_bound (width : Nat) (equations : List Executable.Equation) (first second : Nat)
    (firstBound : first<width+1) (secondBound : second<width+1) :
    (Encoding.rational.encode (cell width equations first second)).length ≤
      8*(Encoding.rationalMatrix.encode (equationMatrix width equations)).length+7 := by
  let left := column (equationMatrix width equations) first
  let right := column (equationMatrix width equations) second
  have equal : left.length=right.length := by simp [left,right]
  have paired : (left.zip right).map (fun pair => pair.1*pair.2)=List.zipWith (·*·) left right := by
    rw [List.map_zip_eq_zipWith]
    rfl
  have result := RowDot.result_length_le_rows (left.zip right)
  simp only [List.map_fst_zip equal.le,List.map_snd_zip equal.ge,paired] at result
  have leftSize := MatrixColumn.column_length_le (equationMatrix width equations) left first
    (equationMatrix_column_selected width equations ⟨first,firstBound⟩)
  have rightSize := MatrixColumn.column_length_le (equationMatrix width equations) right second
    (equationMatrix_column_selected width equations ⟨second,secondBound⟩)
  change (Encoding.rational.encode (cell width equations first second)).length ≤ _ at result
  omega

theorem columnBody_executes (width : Nat) (equations : List Executable.Equation) (first second : Nat)
    (firstBound : first<width) (secondBound : second<width+1) (columns rows rowRev matrixRev : List Bool) :
    ∃ time ≤ columnBudget (Encoding.rationalMatrix.encode (equationMatrix width equations)).length width,
      Executes columnBody (state width equations first second columns rows rowRev matrixRev []) time
        (state width equations first (second+1) columns rows
          ((Encoding.frame (Encoding.rational.encode (cell width equations first second))).reverse++rowRev) matrixRev []) := by
  let value := Encoding.rational.encode (cell width equations first second)
  let initial := state width equations first second columns rows rowRev matrixRev value
  let emitted := state width equations first second columns rows ((Encoding.frame value).reverse++rowRev) matrixRev []
  obtain ⟨entryTime,entryBound,a⟩ := localEntry_executes width equations first second firstBound secondBound columns rows rowRev matrixRev
  have b := emitScalar_executes initial rfl rfl
  have bStore : Function.update (Function.update initial 42 []) 47 ((Encoding.frame (initial 42)).reverse++initial 47)=emitted := by
    funext r;fin_cases r <;> simp [initial,emitted,state,outerBank,ready,bank]
  rw [bStore] at b
  change Executes _ initial (9*value.length+8) emitted at b
  have c := pushBit_executes (39 : Fin 53) true emitted
  have cStore : Function.update emitted 39 (true::emitted 39)=
      state width equations first (second+1) columns rows ((Encoding.frame value).reverse++rowRev) matrixRev [] := by
    funext r;fin_cases r <;> simp [emitted,state,outerBank,ready,bank,List.replicate_succ]
  rw [cStore] at c
  refine ⟨_,?_,a.sequence (b.sequence c)⟩
  have resultBound := cell_length_bound width equations first second (by omega) secondBound
  have power := Nat.pow_le_pow_left (show (Encoding.rationalMatrix.encode (equationMatrix width equations)).length+first+second+3 ≤
    (Encoding.rationalMatrix.encode (equationMatrix width equations)).length+2*width+3 by omega) 4
  dsimp only [columnBudget,value]
  omega

end Counting.StackMachine.GaussianNormal
