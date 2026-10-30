import Counting.StackGaussianNormalRow

namespace Counting.StackMachine.GaussianNormal
open Routine GaussianNormalMatrix
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

abbrev rowsLoop : Routine 51 := forEach 46 rowBody

def matrixRows (width : Nat) (equations : List Executable.Equation) (start count : Nat) : List (List Rat) :=
  (List.range' start count).map (fun first => columnValues width equations first 0 (width+1))

@[simp] theorem matrixRows_length (width : Nat) (equations : List Executable.Equation) (start count : Nat) :
    (matrixRows width equations start count).length=count := by simp [matrixRows]

theorem matrixRows_full (width : Nat) (equations : List Executable.Equation) :
    matrixRows width equations 0 width=StoredGaussian.augmentedMatrix (Executable.normalSystem width equations) := by
  apply List.ext_getElem (by simp)
  intro index leftBound rightBound
  have inside : index<width := by simpa using leftBound
  simp only [matrixRows,List.getElem_map,List.getElem_range',Nat.one_mul,Nat.zero_add,
    StoredGaussian.augmentedMatrix,List.getElem_ofFn]
  exact columnValues_full width equations ⟨index,inside⟩

/-- Both nested loops are countdown programs on actual unary registers.
This theorem includes width zero and returns exactly the original
materialized normal-system matrix in its serialized row order. -/
theorem rowsLoop_executes (width : Nat) (equations : List Executable.Equation) (start count : Nat)
    (inside : start+count≤width) (matrixRev : List Bool) :
    ∃ time ≤ count*(rowBudget (Encoding.rationalMatrix.encode (equationMatrix width equations)).length width+2)+1,
      Executes rowsLoop (state width equations start 0 [] (List.replicate count true) [] matrixRev []) time
        (state width equations (start+count) 0 [] [] []
          ((Encoding.sequence (Encoding.framed Encoding.rationalRow) (matrixRows width equations start count)).reverse++matrixRev) []) := by
  induction count generalizing start matrixRev with
  | zero =>
    have ran := repeat_empty (46 : Fin 53) rowBody (state width equations start 0 [] [] [] matrixRev []) rfl
    exact ⟨1,by simp,⟨⟨1,_⟩,ran.1,ran.2,rfl⟩⟩
  | succ count ih =>
    let first : Fin width := ⟨start,by omega⟩
    let row := StoredGaussian.augmentedRow (Executable.normalSystem width equations) first
    let tailCounter := List.replicate count true
    let initial := state width equations start 0 [] (true::tailCounter) [] matrixRev []
    let nextRev := (Encoding.frame (Encoding.rationalRow.encode row)).reverse++matrixRev
    have popped : Function.update initial 46 tailCounter=
        state width equations start 0 [] tailCounter [] matrixRev [] := by
      funext r;fin_cases r <;> simp [initial,state,outerBank]
    obtain ⟨bodyTime,bodyBound,bodyFinish,bodyRun,bodyHalt,bodyStore⟩ :=
      rowBody_executes width equations first tailCounter matrixRev
    have firstRun := repeat_iteration (46 : Fin 53) rowBody initial true tailCounter rfl bodyTime bodyFinish
      (by rw [popped];exact bodyRun) bodyHalt
    obtain ⟨tailTime,tailBound,tailFinish,tailRun,tailHalt,tailStore⟩ :=
      ih (start+1) (by omega) nextRev
    refine ⟨bodyTime+2+tailTime,?_,⟨tailFinish,?_,tailHalt,?_⟩⟩
    · nlinarith
    · have combined := Machine.run_add (step rowsLoop.program) (bodyTime+2) tailTime ⟨0,initial⟩
      rw [firstRun,Option.bind_some,bodyStore,tailRun] at combined
      simpa only [initial,tailCounter,List.replicate_succ] using combined
    · rw [tailStore]
      simp only [matrixRows,List.range'_succ,List.map_cons,Encoding.sequence,Encoding.framed,
        List.reverse_append,List.append_assoc]
      rw [columnValues_full width equations first]
      simp only [nextRev,row,Nat.add_comm,Nat.add_left_comm]

end Counting.StackMachine.GaussianNormal
