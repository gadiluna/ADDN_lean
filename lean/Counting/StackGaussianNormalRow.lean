import Counting.StackGaussianNormalColumnLoop
import Counting.StackGaussianNormalFinishRow

namespace Counting.StackMachine.GaussianNormal
open Routine GaussianNormalMatrix
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

abbrev initializeColumns : Routine 51 := sequence (ofProgram (ListPrograms.copyProgram 50 44 45 52)) (pushBit 45 true)
abbrev resetColumn : Routine 51 := sequence (clear 39) (pushBit 39 true)
abbrev rowBody : Routine 51 := sequence initializeColumns (sequence columnLoop
  (sequence finishRow (sequence resetColumn (pushBit 38 true))))

def rowBudget (size width : Nat) : Nat :=
  (width+1)*(columnBudget size width+2)+11*(width+1)*(16*size+15)+100*(width+1)+100

theorem initializeColumns_executes (width : Nat) (equations : List Executable.Equation) (first : Nat)
    (rows matrixRev : List Bool) :
    Executes initializeColumns (state width equations first 0 [] rows [] matrixRev []) (5*width+4)
      (state width equations first 0 (List.replicate (width+1) true) rows [] matrixRev []) := by
  let initial := state width equations first 0 [] rows [] matrixRev []
  let copied := state width equations first 0 (List.replicate width true) rows [] matrixRev []
  have a := copy_executes 50 (44 : Fin 53) 45 52 (by decide) (by decide) (by decide) initial rfl
  have aStore : Function.update initial 45 (initial 44++initial 45)=copied := by
    funext r;fin_cases r <;> simp [initial,copied,state,outerBank]
  rw [aStore] at a
  change Executes _ initial (5*(List.replicate width true).length+2) copied at a
  rw [List.length_replicate] at a
  have b := pushBit_executes (45 : Fin 53) true copied
  have bStore : Function.update copied 45 (true::copied 45)=
      state width equations first 0 (List.replicate (width+1) true) rows [] matrixRev [] := by
    funext r;fin_cases r <;> simp [copied,state,outerBank,List.replicate_succ]
  rw [bStore] at b
  convert a.sequence b using 1

theorem resetColumn_executes (width : Nat) (equations : List Executable.Equation) (first second : Nat)
    (rows matrixRev : List Bool) :
    Executes resetColumn (state width equations first second [] rows [] matrixRev []) (second+4)
      (state width equations first 0 [] rows [] matrixRev []) := by
  let initial := state width equations first second [] rows [] matrixRev []
  have a := clear_executes (39 : Fin 53) initial
  let cleared := Function.update initial 39 []
  have b := pushBit_executes (39 : Fin 53) true cleared
  have final : Function.update cleared 39 (true::cleared 39)=state width equations first 0 [] rows [] matrixRev [] := by
    funext r;fin_cases r <;> simp [cleared,initial,state,outerBank,ready,bank]
  rw [final] at b
  have combined := a.sequence b
  convert combined using 1
  simp [initial,state,outerBank,ready,bank]

theorem columnValues_fields_bound (width : Nat) (equations : List Executable.Equation) (first start count : Nat)
    (firstBound : first<width+1) (inside : start+count≤width+1) :
    (Encoding.sequence (Encoding.framed Encoding.rational) (columnValues width equations first start count)).length ≤
      count*(16*(Encoding.rationalMatrix.encode (equationMatrix width equations)).length+15) := by
  induction count generalizing start with
  | zero => simp [columnValues,Encoding.sequence]
  | succ count ih =>
    have tailBound := ih (start+1) (by omega)
    have current := cell_length_bound width equations first start firstBound (by omega)
    simp only [columnValues,List.range'_succ,List.map_cons,Encoding.sequence,List.length_append,Encoding.framed_length] at *
    nlinarith

theorem rowBody_executes (width : Nat) (equations : List Executable.Equation) (first : Fin width)
    (rows matrixRev : List Bool) :
    ∃ time ≤ rowBudget (Encoding.rationalMatrix.encode (equationMatrix width equations)).length width,
      Executes rowBody (state width equations first.val 0 [] rows [] matrixRev []) time
        (state width equations (first.val+1) 0 [] rows []
          ((Encoding.frame (Encoding.rationalRow.encode (StoredGaussian.augmentedRow (Executable.normalSystem width equations) first))).reverse++matrixRev) []) := by
  let row := StoredGaussian.augmentedRow (Executable.normalSystem width equations) first
  let fields := Encoding.sequence (Encoding.framed Encoding.rational) row
  let nextMatrix := (Encoding.frame (Encoding.rationalRow.encode row)).reverse++matrixRev
  have a := initializeColumns_executes width equations first.val rows matrixRev
  obtain ⟨loopTime,loopBound,b⟩ := columnLoop_executes width equations first.val 0 (width+1) first.isLt (by omega) rows [] matrixRev
  rw [columnValues_full width equations first] at b
  simp only [Nat.zero_add,List.append_nil] at b
  let afterLoop := state width equations first.val (width+1) [] rows fields.reverse matrixRev []
  have c := finishRow_executes afterLoop rfl rfl rfl rfl
  have rowEncoding : Encoding.natural.encode (width+1)++fields=Encoding.rationalRow.encode row := by
    have length : row.length=width+1 := by simp [row]
    change _=Encoding.natural.encode row.length++fields
    rw [length]
  have cStore : Function.update (Function.update afterLoop 47 []) 48
      ((Encoding.frame (afterLoop 49++(afterLoop 47).reverse)).reverse++afterLoop 48)=
      state width equations first.val (width+1) [] rows [] nextMatrix [] := by
    funext r;fin_cases r <;> simp [afterLoop,state,outerBank,ready,bank,nextMatrix,rowEncoding]
  rw [cStore] at c
  change Executes _ afterLoop (11*fields.reverse.length+14*(Encoding.natural.encode (width+1)).length+13) _ at c
  rw [List.length_reverse] at c
  have d := resetColumn_executes width equations first.val (width+1) rows nextMatrix
  have e := pushBit_executes (38 : Fin 53) true (state width equations first.val 0 [] rows [] nextMatrix [])
  have eStore : Function.update (state width equations first.val 0 [] rows [] nextMatrix []) 38
      (true::state width equations first.val 0 [] rows [] nextMatrix [] 38)=
      state width equations (first.val+1) 0 [] rows [] nextMatrix [] := by
    funext r;fin_cases r <;> simp [state,outerBank,ready,bank,List.replicate_succ]
  rw [eStore] at e
  refine ⟨_,?_,a.sequence (b.sequence (c.sequence (d.sequence e)))⟩
  have fieldBound := columnValues_fields_bound width equations first.val 0 (width+1) (by omega) (by omega)
  rw [columnValues_full width equations first] at fieldBound
  have headerBound : (Encoding.natural.encode (width+1)).length ≤ 2*(width+1)+1 := by
    rw [Encoding.natural_length]
    have bits : (width+1).size≤width+1 := Nat.size_le.mpr Nat.lt_two_pow_self
    omega
  change fields.length ≤ _ at fieldBound
  dsimp only [rowBudget]
  nlinarith

end Counting.StackMachine.GaussianNormal
