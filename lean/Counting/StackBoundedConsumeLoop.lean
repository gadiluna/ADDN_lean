import Counting.StackDescendingEmit

namespace Counting.StackMachine.Routine

/-- A loop body is invoked only after a nonempty counter has been consumed.
This exposes the strict bound needed for finite indices without requiring
execution of the body at the unused upper endpoint. -/
theorem forEach_bounded_afterConsume {registers : Nat} (counter : Fin (registers+2)) (routine : Routine registers)
    (body : Store registers → Store registers) (invariant : Store registers → Prop) (bodyBound : Nat)
    (executes : ∀ store, invariant store → store counter ≠ [] → ∃ time ≤ bodyBound,
      Executes routine (consume counter store) time (body (consume counter store)))
    (preservesCounter : ∀ store, invariant store → body store counter = store counter)
    (consumeInvariant : ∀ store, invariant store → invariant (consume counter store))
    (bodyInvariant : ∀ store, invariant store → invariant (body store))
    (count : Nat) (store : Store registers) (valid : invariant store) (length : (store counter).length=count) :
    ∃ transitions ≤ count*(bodyBound+2)+1,
      Executes (forEach counter routine) store transitions ((iteration counter body)^[count] store) := by
  induction count generalizing store with
  | zero =>
      have empty : store counter=[] := List.length_eq_zero_iff.mp length
      obtain ⟨ran,halted⟩ := repeat_empty counter routine store empty
      exact ⟨1,by simp,⟨1,store⟩,ran,halted,rfl⟩
  | succ count ih =>
      cases contents : store counter with
      | nil => simp only [contents,List.length_nil] at length; omega
      | cons bit rest =>
          have consumedValid := consumeInvariant store valid
          obtain ⟨bodyTime,bodyBounded,middle,bodyRun,bodyHalt,bodyStore⟩ := executes store valid (by simp [contents])
          have nextLength : ((iteration counter body store) counter).length=count := by
            change (body (consume counter store) counter).length=count
            rw [preservesCounter _ consumedValid]
            simp only [consume,Function.update_self,contents,List.tail_cons]
            simp only [contents,List.length_cons] at length
            omega
          obtain ⟨tailTime,tailBounded,finish,tailRun,tailHalt,tailStore⟩ :=
            ih (iteration counter body store) (bodyInvariant _ consumedValid) nextLength
          have firstRun := repeat_iteration counter routine store bit rest contents bodyTime middle
            (by simpa only [consume,contents,List.tail_cons] using bodyRun) bodyHalt
          have changed : middle.store=iteration counter body store := bodyStore
          refine ⟨bodyTime+2+tailTime,?_,finish,?_,tailHalt,?_⟩
          · nlinarith
          · rw [Machine.run_add,firstRun,Option.bind_some,changed,tailRun]
          · rw [Function.iterate_succ_apply]
            exact tailStore

theorem descendingEmit_afterConsume {registers : Nat} (counter output : Fin (registers+2))
    (distinct : counter ≠ output) (routine : Routine registers) (chunk : Nat → List Bool)
    (invariant : Store registers → Prop) (bodyBound : Nat)
    (bodyExecutes : ∀ store, invariant store → store counter ≠ [] → ∃ time ≤ bodyBound,
      Executes routine (consume counter store) time (emitBody counter output chunk (consume counter store)))
    (consumeInvariant : ∀ store, invariant store → invariant (consume counter store))
    (emitInvariant : ∀ store, invariant store → invariant (emitBody counter output chunk store))
    (store : Store registers) (valid : invariant store) :
    ∃ transitions ≤ (store counter).length*(bodyBound+2)+1,
      Executes (forEach counter routine) store transitions
        (Function.update (Function.update store counter []) output
          (emittedChunks chunk (store counter).length++store output)) := by
  obtain ⟨time,bounded,executed⟩ := forEach_bounded_afterConsume counter routine (emitBody counter output chunk) invariant bodyBound
    bodyExecutes (fun store _ => by simp [emitBody,distinct]) consumeInvariant emitInvariant
    (store counter).length store valid rfl
  rw [iterate_emitBody counter output distinct chunk _ store rfl] at executed
  exact ⟨time,bounded,executed⟩

end Counting.StackMachine.Routine
