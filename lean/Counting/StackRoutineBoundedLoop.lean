import Counting.StackRoutineSemantics

namespace Counting.StackMachine.Routine

/-- A bounded loop whose body has a proved, possibly data-dependent running
time. The body contract is required only on the maintained invariant. -/
theorem forEach_bounded {registers : Nat} (counter : Fin (registers+2)) (routine : Routine registers)
    (body : Store registers → Store registers) (invariant : Store registers → Prop) (bodyBound : Nat)
    (executes : ∀ store, invariant store → ∃ time ≤ bodyBound, Executes routine store time (body store))
    (preservesCounter : ∀ store, invariant store → body store counter = store counter)
    (consumeInvariant : ∀ store, invariant store → invariant (consume counter store))
    (bodyInvariant : ∀ store, invariant store → invariant (body store))
    (count : Nat) (store : Store registers) (valid : invariant store) (length : (store counter).length = count) :
    ∃ transitions ≤ count*(bodyBound+2)+1,
      Executes (forEach counter routine) store transitions ((iteration counter body)^[count] store) := by
  induction count generalizing store with
  | zero =>
      have empty : store counter = [] := List.length_eq_zero_iff.mp length
      obtain ⟨ran,halted⟩ := repeat_empty counter routine store empty
      exact ⟨1,by simp,⟨1,store⟩,ran,halted,rfl⟩
  | succ count ih =>
      cases contents : store counter with
      | nil => simp only [contents,List.length_nil] at length; omega
      | cons bit rest =>
          have consumedValid := consumeInvariant store valid
          obtain ⟨bodyTime,bodyBounded,middle,bodyRun,bodyHalt,bodyStore⟩ := executes (consume counter store) consumedValid
          have nextLength : ((iteration counter body store) counter).length = count := by
            change (body (consume counter store) counter).length = count
            rw [preservesCounter _ consumedValid]
            simp only [consume,Function.update_self,contents,List.tail_cons]
            simp only [contents,List.length_cons] at length
            omega
          obtain ⟨tailTime,tailBounded,finish,tailRun,tailHalt,tailStore⟩ :=
            ih (iteration counter body store) (bodyInvariant _ consumedValid) nextLength
          have firstRun := repeat_iteration counter routine store bit rest contents bodyTime middle
            (by simpa only [consume,contents,List.tail_cons] using bodyRun) bodyHalt
          have changed : middle.store = iteration counter body store := bodyStore
          refine ⟨bodyTime+2+tailTime,?_,finish,?_,tailHalt,?_⟩
          · nlinarith
          · rw [Machine.run_add,firstRun,Option.bind_some,changed,tailRun]
          · rw [Function.iterate_succ_apply]
            exact tailStore

end Counting.StackMachine.Routine
