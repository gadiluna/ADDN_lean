import Counting.StackGaussianRhsStep
import Counting.StackLoop

namespace Counting.StackMachine.GaussianRhs
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

abbrev loop : Routine 11 := forEach 10 body

theorem loop_executes (rows : List (List Rat)) (values : List Rat) (column : Nat)
    (selected : List.Forall₂ (fun row value => row[column]?=some value) rows values)
    (limit : Nat) (bounded : ∀ row∈rows,(Encoding.rationalRow.encode row).length ≤ limit)
    (suffix output header : List Bool) :
    ∃ time ≤ rows.length*(100*(limit+column+2)+2)+1,
      Executes loop
        (state (Encoding.sequence (Encoding.framed Encoding.rationalRow) rows++suffix) output column
          (List.replicate rows.length true) header) time
        (state suffix ((Encoding.sequence (Encoding.framed Encoding.rational) values).reverse++output) column [] header) := by
  induction selected generalizing suffix output header with
  | nil =>
    have ran := repeat_empty (10 : Fin 13) body (state suffix output column [] header) rfl
    exact ⟨1,by simp,⟨⟨1,_⟩,ran.1,ran.2,rfl⟩⟩
  | @cons row value rows values selected tail ih =>
    let rest := Encoding.sequence (Encoding.framed Encoding.rationalRow) rows++suffix
    let firstCode := Encoding.frame (Encoding.rationalRow.encode row)
    let valueCode := Encoding.frame (Encoding.rational.encode value)
    let initial := state (firstCode++rest) output column (true::List.replicate rows.length true) header
    have popped : Function.update initial 10 (List.replicate rows.length true)=
        state (firstCode++rest) output column (List.replicate rows.length true) header := by
      funext r;fin_cases r <;> simp [initial,state,file]
    obtain ⟨bodyTime,bodyBound,bodyFinish,bodyRun,bodyHalt,bodyStore⟩ :=
      body_executes row value column selected rest output (List.replicate rows.length true) header
    have first := repeat_iteration (10 : Fin 13) body initial true (List.replicate rows.length true) rfl
      bodyTime bodyFinish (by rw [popped];exact bodyRun) bodyHalt
    obtain ⟨tailTime,tailBound,tailFinish,tailRun,tailHalt,tailStore⟩ :=
      ih (fun item present => bounded item (by simp [present])) suffix (valueCode.reverse++output) header
    refine ⟨bodyTime+2+tailTime,?_,⟨tailFinish,?_,?_⟩⟩
    · have firstBound := bounded row (by simp)
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
    · have combined := Machine.run_add (step loop.program) (bodyTime+2) tailTime ⟨0,initial⟩
      rw [first,Option.bind_some,bodyStore,tailRun] at combined
      simpa only [initial,firstCode,rest,Encoding.sequence,Encoding.framed,List.append_assoc,
        List.length_cons,List.replicate_succ] using combined
    · refine ⟨tailHalt,?_⟩
      simpa only [Encoding.sequence,Encoding.framed,List.reverse_append,List.append_assoc,valueCode] using tailStore

end Counting.StackMachine.GaussianRhs
