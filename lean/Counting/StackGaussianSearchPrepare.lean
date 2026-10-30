import Counting.StackGaussianSearch
import Counting.StackLookupDrop

namespace Counting.StackMachine.GaussianBank
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

abbrev popOne (target : Fin 52) : Routine 50 :=
  ⟨1,fun control => if control=0 then .pop target 1 1 1 else .halt⟩

theorem popOne_executes (target : Fin 52) (store : Fin 52 → List Bool) (bit : Bool) (rest : List Bool)
    (contents : store target=bit::rest) :
    Executes (popOne target) store 1 (Function.update store target rest) := by
  refine ⟨⟨1,_⟩,?_,?_,rfl⟩
  · simp [Machine.run,step,popOne,contents]
    funext r
    cases decision : instDecidableEqFin 52 r target with
    | isTrue same => simp [Function.update,same]
    | isFalse different => simp [Function.update,different]
  · simp [step,popOne]

abbrev copyCandidate : Routine 50 := ofProgram (ListPrograms.copyProgram 49 42 44 4)
abbrev copyColumn : Routine 50 := ofProgram (ListPrograms.copyProgram 49 42 39 4)
abbrev copyDimension : Routine 50 := ofProgram (ListPrograms.copyProgram 49 43 49 4)
abbrev copySkip : Routine 50 := ofProgram (ListPrograms.copyProgram 49 42 3 4)
abbrev subtractCandidates : Routine 50 := ofProgram (Lookup.dropProgram 50 49 3)
abbrev prepareSearch : Routine 50 := sequence copyCandidate (sequence copyColumn
  (sequence copyDimension (sequence copySkip (sequence (popOne 3)
    (sequence subtractCandidates (pushBit 50 true))))))

/-- Candidate count is computed by actual copies and unary subtraction.
The dimension and pivot registers survive and are not implicit runtime
parameters of the generated program. -/
theorem prepareSearch_executes (matrix : List Bool) (pivot dimension : Nat)
    (saved : Fin 10 → List Bool) (hp : saved 0=List.replicate (pivot+1) true)
    (hd : saved 1=List.replicate dimension true) :
    Executes prepareSearch (searchStore matrix [] [] [] [] saved)
      (17*pivot+5*dimension+32)
      (searchStore matrix (List.replicate (pivot+1) true) (List.replicate (pivot+1) true)
        (List.replicate (dimension-pivot) true) [true] saved) := by
  let p := List.replicate (pivot+1) true
  let d := List.replicate dimension true
  let s0 := searchStore matrix [] [] [] [] saved
  let s1 := searchStore matrix p [] [] [] saved
  let s2 := searchStore matrix p p [] [] saved
  let s3 := searchStore matrix p p d [] saved
  let s4 := Function.update s3 3 p
  let s5 := Function.update s3 3 (List.replicate pivot true)
  let s6 := searchStore matrix p p (List.replicate (dimension-pivot) true) [] saved
  have a := copy_executes 49 (42 : Fin 52) 44 4 (by decide) (by decide) (by decide) s0 rfl
  have aStore : Function.update s0 44 (s0 42++s0 44)=s1 := by
    funext r;fin_cases r <;> simp [s0,s1,p,searchStore,searchSaved,ready,bank,MatrixAxpy.file,RowAxpy.file,hp]
  rw [aStore] at a
  have b := copy_executes 49 (42 : Fin 52) 39 4 (by decide) (by decide) (by decide) s1 rfl
  have bStore : Function.update s1 39 (s1 42++s1 39)=s2 := by
    funext r;fin_cases r <;> simp [s1,s2,p,searchStore,searchSaved,ready,bank,MatrixAxpy.file,RowAxpy.file,hp]
  rw [bStore] at b
  have c := copy_executes 49 (43 : Fin 52) 49 4 (by decide) (by decide) (by decide) s2 rfl
  have cStore : Function.update s2 49 (s2 43++s2 49)=s3 := by
    funext r;fin_cases r <;> simp [s2,s3,d,searchStore,searchSaved,ready,bank,MatrixAxpy.file,RowAxpy.file,hd]
  rw [cStore] at c
  have e := copy_executes 49 (42 : Fin 52) 3 4 (by decide) (by decide) (by decide) s3 rfl
  have eStore : Function.update s3 3 (s3 42++s3 3)=s4 := by
    simp [s4,s3,p,searchStore,searchSaved,ready,bank,MatrixAxpy.file,RowAxpy.file,hp]
  rw [eStore] at e
  have f := popOne_executes 3 s4 true (List.replicate pivot true) (by simp [s4,p,List.replicate_succ])
  have fStore : Function.update s4 3 (List.replicate pivot true)=s5 := by simp [s4,s5]
  rw [fStore] at f
  have g := Lookup.drop_executes 50 (49 : Fin 52) 3 (by decide) s5
  have gStore : Function.update (Function.update s5 3 []) 49 ((s5 49).drop (s5 3).length)=s6 := by
    funext r;fin_cases r <;> simp [s5,s3,s6,p,d,searchStore,searchSaved,ready,bank,MatrixAxpy.file,RowAxpy.file]
  rw [gStore] at g
  have h := pushBit_executes (50 : Fin 52) true s6
  have hStore : Function.update s6 50 (true::s6 50)=
      searchStore matrix p p (List.replicate (dimension-pivot) true) [true] saved := by
    funext r;fin_cases r <;> simp [s6,searchStore,searchSaved,ready,bank,MatrixAxpy.file,RowAxpy.file]
  rw [hStore] at h
  have aTime : (s0 42).length=pivot+1 := by simp [s0,searchStore,searchSaved,ready,bank,hp]
  have bTime : (s1 42).length=pivot+1 := by simp [s1,searchStore,searchSaved,ready,bank,hp]
  have cTime : (s2 43).length=dimension := by simp [s2,searchStore,searchSaved,ready,bank,hd]
  have eTime : (s3 42).length=pivot+1 := by simp [s3,searchStore,searchSaved,ready,bank,hp]
  have gTime : (s5 3).length=pivot := by simp [s5]
  rw [aTime] at a
  rw [bTime] at b
  rw [cTime] at c
  rw [eTime] at e
  rw [gTime] at g
  simp +instances only [ListPrograms.copyProgram] at a b c e
  simp +instances only [Lookup.dropProgram] at g
  convert a.sequence (b.sequence (c.sequence (e.sequence (f.sequence (g.sequence h))))) using 1
  all_goals try rfl
  all_goals omega

end Counting.StackMachine.GaussianBank
