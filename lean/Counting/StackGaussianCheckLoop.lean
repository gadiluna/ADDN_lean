import Counting.StackGaussianCheckStep
import Counting.GaussianEquationCheck

namespace Counting.StackMachine.GaussianCheck
open Routine GaussianEquationCheck
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

abbrev loop : Routine 41 := forEach 38 body

def rowBudget (size vectorSize : Nat) : Nat := 100000000000000*(size+vectorSize+1)^4

/-- Every row is read, even after a failed equation. The returned Boolean
is the conjunction of the actual exact-arithmetic dot-product tests. -/
theorem loop_executes (rows : List (List Rat)) (solution : List Rat) (size : Nat)
    (same : ∀ row∈rows,row.length=solution.length)
    (bounded : ∀ row∈rows,(Encoding.rationalRow.encode row).length≤ size)
    (suffix : List Bool) (accepted : Bool) :
    ∃ time ≤ rows.length*(rowBudget size (Encoding.rationalRow.encode solution).length+2)+1,
      Executes loop (file [] [] [] (Encoding.sequence (Encoding.framed Encoding.rationalRow) rows++suffix)
        (Encoding.rationalRow.encode solution) (List.replicate rows.length true) [accepted] []) time
        (file [] [] [] suffix (Encoding.rationalRow.encode solution) []
          [accepted && accepts rows solution] []) := by
  induction rows generalizing accepted with
  | nil =>
    have ran := repeat_empty (38:Fin 43) body
      (file [] [] [] suffix (Encoding.rationalRow.encode solution) [] [accepted] []) rfl
    exact ⟨1,by simp,⟨⟨1,_⟩,ran.1,ran.2,by simp [accepts]⟩⟩
  | cons row rows ih =>
    let tail := Encoding.sequence (Encoding.framed Encoding.rationalRow) rows++suffix
    let counter := List.replicate rows.length true
    let initial := file [] [] [] (Encoding.frame (Encoding.rationalRow.encode row)++tail)
      (Encoding.rationalRow.encode solution) (true::counter) [accepted] []
    have popped : Function.update initial 38 counter=
        file [] [] [] (Encoding.frame (Encoding.rationalRow.encode row)++tail)
          (Encoding.rationalRow.encode solution) counter [accepted] [] := by
      funext r;fin_cases r <;> simp [initial,file]
    obtain ⟨bodyTime,bodyBound,bodyFinish,bodyRun,bodyHalt,bodyStore⟩ :=
      body_executes row solution (same row (by simp)) tail counter accepted
    have firstRun := repeat_iteration (38:Fin 43) body initial true counter rfl bodyTime bodyFinish
      (by rw [popped];exact bodyRun) bodyHalt
    obtain ⟨tailTime,tailBound,tailFinish,tailRun,tailHalt,tailStore⟩ :=
      ih (by intro value member;exact same value (List.mem_cons_of_mem row member))
        (by intro value member;exact bounded value (List.mem_cons_of_mem row member))
        (accepted && decide ((List.zipWith (·*·) row solution).sum=0))
    have bodyBudget : bodyTime≤ rowBudget size (Encoding.rationalRow.encode solution).length := by
      apply bodyBound.trans
      unfold rowBudget
      gcongr
      exact bounded row (by simp)
    refine ⟨bodyTime+2+tailTime,?_,⟨tailFinish,?_,?_ ,?_⟩⟩
    · simp only [List.length_cons]
      nlinarith
    · have combined := Machine.run_add (step loop.program) (bodyTime+2) tailTime ⟨0,initial⟩
      rw [firstRun,Option.bind_some,bodyStore,tailRun] at combined
      simpa only [initial,counter,tail,Encoding.sequence,Encoding.framed,List.append_assoc,
        List.length_cons,List.replicate_succ] using combined
    · exact tailHalt
    · rw [tailStore]
      simp only [accepts,List.all_cons,Bool.and_assoc,GaussianNormalMatrix.dot]

end Counting.StackMachine.GaussianCheck
