import Counting.StackGaussianNormalColumns

namespace Counting.StackMachine.GaussianNormal
open Routine GaussianNormalMatrix
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

def columnValues (width : Nat) (equations : List Executable.Equation) (first start count : Nat) : List Rat :=
  (List.range' start count).map (cell width equations first)

@[simp] theorem columnValues_length (width : Nat) (equations : List Executable.Equation) (first start count : Nat) :
    (columnValues width equations first start count).length=count := by simp [columnValues]

theorem columnValues_full (width : Nat) (equations : List Executable.Equation) (first : Fin width) :
    columnValues width equations first.val 0 (width+1)=
      StoredGaussian.augmentedRow (Executable.normalSystem width equations) first := by
  rw [normal_row_ofFn]
  apply List.ext_getElem (by simp)
  intro index leftBound rightBound
  simp only [columnValues,List.getElem_map,List.getElem_range',Nat.one_mul,Nat.zero_add,List.getElem_ofFn,cell]

/-- A unary countdown traverses all requested columns in order. The
physical column index is incremented and all encoded result fields are
actually appended to the reversed row stream. -/
theorem columnLoop_executes (width : Nat) (equations : List Executable.Equation) (first start count : Nat)
    (firstBound : first<width) (inside : start+count≤width+1) (rows rowRev matrixRev : List Bool) :
    ∃ time ≤ count*(columnBudget (Encoding.rationalMatrix.encode (equationMatrix width equations)).length width+2)+1,
      Executes columnLoop (state width equations first start (List.replicate count true) rows rowRev matrixRev []) time
        (state width equations first (start+count) [] rows
          ((Encoding.sequence (Encoding.framed Encoding.rational) (columnValues width equations first start count)).reverse++rowRev)
          matrixRev []) := by
  induction count generalizing start rowRev with
  | zero =>
    have ran := repeat_empty (45 : Fin 53) columnBody (state width equations first start [] rows rowRev matrixRev []) rfl
    exact ⟨1,by simp,⟨⟨1,_⟩,ran.1,ran.2,rfl⟩⟩
  | succ count ih =>
    let tailCounter := List.replicate count true
    let initial := state width equations first start (true::tailCounter) rows rowRev matrixRev []
    let nextRev := (Encoding.frame (Encoding.rational.encode (cell width equations first start))).reverse++rowRev
    have popped : Function.update initial 45 tailCounter=
        state width equations first start tailCounter rows rowRev matrixRev [] := by
      funext r;fin_cases r <;> simp [initial,state,outerBank]
    obtain ⟨bodyTime,bodyBound,bodyFinish,bodyRun,bodyHalt,bodyStore⟩ :=
      columnBody_executes width equations first start firstBound (by omega) tailCounter rows rowRev matrixRev
    have firstRun := repeat_iteration (45 : Fin 53) columnBody initial true tailCounter rfl bodyTime bodyFinish
      (by rw [popped];exact bodyRun) bodyHalt
    obtain ⟨tailTime,tailBound,tailFinish,tailRun,tailHalt,tailStore⟩ :=
      ih (start+1) (by omega) nextRev
    refine ⟨bodyTime+2+tailTime,?_,⟨tailFinish,?_,tailHalt,?_⟩⟩
    · nlinarith
    · have combined := Machine.run_add (step columnLoop.program) (bodyTime+2) tailTime ⟨0,initial⟩
      rw [firstRun,Option.bind_some,bodyStore,tailRun] at combined
      simpa only [initial,tailCounter,List.replicate_succ] using combined
    · rw [tailStore]
      simp only [columnValues,List.range'_succ,List.map_cons,Encoding.sequence,Encoding.framed,
        List.reverse_append,List.append_assoc]
      simp only [nextRev,Nat.add_comm,Nat.add_left_comm]

end Counting.StackMachine.GaussianNormal
