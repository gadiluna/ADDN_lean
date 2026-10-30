import Counting.StackGaussianState

namespace Counting.StackMachine.GaussianBank
open Routine DirectedCounting.VerifiedGaussianAnchorSolver RationalSystem
set_option backward.isDefEq.respectTransparency false

theorem clearSaved_executes (index : Fin 10) (matrix factor first second : List Bool)
    (saved : Fin 10 → List Bool) :
    Executes (clear (savedRole index)) (ready matrix factor first second saved) ((saved index).length+1)
      (ready matrix factor first second (Function.update saved index [])) := by
  have ran := clear_executes (savedRole index) (ready matrix factor first second saved)
  rw [ready_saved,update_saved] at ran
  exact ran

theorem pushSaved_executes (index : Fin 10) (bit : Bool) (matrix factor first second : List Bool)
    (saved : Fin 10 → List Bool) :
    Executes (pushBit (savedRole index) bit) (ready matrix factor first second saved) 1
      (ready matrix factor first second (Function.update saved index (bit::saved index))) := by
  have ran := pushBit_executes (savedRole index) bit (ready matrix factor first second saved)
  rw [ready_saved,update_saved] at ran
  exact ran

abbrev setSavedFlag (index : Fin 10) (bit : Bool) : Routine 50 :=
  sequence (clear (savedRole index)) (pushBit (savedRole index) bit)

theorem setSavedFlag_executes (index : Fin 10) (bit : Bool) (matrix factor first second : List Bool)
    (saved : Fin 10 → List Bool) :
    Executes (setSavedFlag index bit) (ready matrix factor first second saved) ((saved index).length+3)
      (ready matrix factor first second (Function.update saved index [bit])) := by
  have firstRun := clearSaved_executes index matrix factor first second saved
  have secondRun := pushSaved_executes index bit matrix factor first second (Function.update saved index [])
  simp only [Function.update_self,Function.update_idem] at secondRun
  convert firstRun.sequence secondRun using 1

abbrev failSearch : Routine 50 := sequence (clear 44) (sequence (clear 50) (setSavedFlag 3 false))

theorem failSearch_executes {q : Nat} (state : GaussianState q) (pivot result : Nat) :
    Executes failSearch (stateStore state pivot (List.replicate (result+1) true) [] [] [true])
      (result+10) (stateStore state.fail pivot [] [] [] []) := by
  let matrix := Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix state.system)
  let saved := stateSaved state pivot (List.replicate (result+1) true) [] [] [true]
  have a := clearSaved_executes 2 matrix [] [] [] saved
  have aStore : Function.update saved 2 []=stateSaved state pivot [] [] [] [true] := by
    funext r;fin_cases r <;> simp [saved,stateSaved]
  rw [aStore] at a
  have b := clearSaved_executes 8 matrix [] [] [] (stateSaved state pivot [] [] [] [true])
  have bStore : Function.update (stateSaved state pivot [] [] [] [true]) 8 []=stateSaved state pivot [] [] [] [] := by
    funext r;fin_cases r <;> simp [stateSaved]
  rw [bStore] at b
  have c := setSavedFlag_executes 3 false matrix [] [] [] (stateSaved state pivot [] [] [] [])
  have cStore : Function.update (stateSaved state pivot [] [] [] []) 3 [false]=stateSaved state.fail pivot [] [] [] [] := by
    funext r;fin_cases r <;> simp [stateSaved,GaussianState.fail]
  rw [cStore] at c
  have aTime : (saved 2).length+1=result+2 := by simp [saved,stateSaved]
  rw [aTime] at a
  change Executes (clear 50) _ 2 _ at b
  change Executes (setSavedFlag 3 false) _ 4 _ at c
  convert a.sequence (b.sequence c) using 1
  all_goals rfl

abbrev initializeRows : Routine 50 := sequence
  (ofProgram (ListPrograms.copyProgram 49 43 49 1)) (pushBit 48 true)

theorem initializeRows_executes {q : Nat} (state : GaussianState q) (pivot : Nat) :
    Executes initializeRows (stateStore state pivot [] [] [] []) (5*q+4)
      (stateStore state pivot [] [true] (List.replicate q true) []) := by
  let initial := stateStore state pivot [] [] [] []
  let copied := stateStore state pivot [] [] (List.replicate q true) []
  have a := copy_executes 49 (43 : Fin 52) 49 1 (by decide) (by decide) (by decide) initial rfl
  have aStore : Function.update initial 49 (initial 43++initial 49)=copied := by
    funext r;fin_cases r <;> simp [initial,copied,stateStore,stateSaved,ready,bank,MatrixAxpy.file,RowAxpy.file]
  rw [aStore] at a
  have aTime : (initial 43).length=q := by simp [initial,stateStore,stateSaved,ready,bank]
  rw [aTime] at a
  have b := pushBit_executes (48 : Fin 52) true copied
  have bStore : Function.update copied 48 (true::copied 48)=stateStore state pivot [] [true] (List.replicate q true) [] := by
    funext r;fin_cases r <;> simp [copied,stateStore,stateSaved,ready,bank,MatrixAxpy.file,RowAxpy.file]
  rw [bStore] at b
  simp +instances only [ListPrograms.copyProgram] at a
  convert a.sequence b using 1
  all_goals rfl

theorem incrementRow_executes {q : Nat} (state : GaussianState q) (pivot row : Nat) (counter : List Bool) :
    Executes (pushBit (48 : Fin 52) true)
      (stateStore state pivot [] (List.replicate (row+1) true) counter []) 1
      (stateStore state pivot [] (List.replicate (row+2) true) counter []) := by
  have ran := pushBit_executes (48 : Fin 52) true
    (stateStore state pivot [] (List.replicate (row+1) true) counter [])
  convert ran using 1
  funext r;fin_cases r <;> simp [stateStore,stateSaved,ready,bank,MatrixAxpy.file,RowAxpy.file,List.replicate_succ]

end Counting.StackMachine.GaussianBank
