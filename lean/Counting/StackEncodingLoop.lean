import Counting.StackEncodingBranch

namespace Counting.StackMachine.EncodingPrograms

/-- Invariant-based bounded iteration over an explicit input-sized register.
The bound includes each loop pop, return jump, and final empty pop. -/
theorem forEach_executes_bounded {extra : Nat} (counter : Fin (extra+2)) (body : Routine extra)
    (transform : Routine.Store extra → Routine.Store extra)
    (invariant : Routine.Store extra → Prop) (bodyBound : Nat)
    (executes : ∀ store, invariant store → ∃ time≤bodyBound,
      Routine.Executes body (Routine.consume counter store) time (transform (Routine.consume counter store)))
    (preserved : ∀ store, invariant store → invariant (Routine.iteration counter transform store))
    (counterPreserved : ∀ store, transform store counter=store counter)
    (count : Nat) (store : Routine.Store extra) (length : (store counter).length=count)
    (valid : invariant store) :
    ∃ time≤count*(bodyBound+2)+1,
      Routine.Executes (Routine.forEach counter body) store time
        ((Routine.iteration counter transform)^[count] store) := by
  induction count generalizing store with
  | zero =>
    have empty : store counter=[] := List.length_eq_zero_iff.mp length
    obtain ⟨ran,halted⟩:=Routine.repeat_empty counter body store empty
    exact ⟨1,by simp,⟨⟨1,store⟩,ran,halted,rfl⟩⟩
  | succ count ih =>
    cases contents : store counter with
    | nil => simp only [contents,List.length_nil] at length; omega
    | cons bit rest =>
      obtain ⟨bodyTime,bodyTimeBound,middle,bodyRun,bodyHalt,bodyStore⟩:=executes store valid
      have nextLength : ((Routine.iteration counter transform store) counter).length=count := by
        simp only [Routine.iteration,counterPreserved,Routine.consume,Function.update_self,contents,List.tail_cons]
        simp only [contents,List.length_cons] at length
        omega
      obtain ⟨tailTime,tailTimeBound,finish,tailRun,tailHalt,tailStore⟩:=
        ih (Routine.iteration counter transform store) nextLength (preserved store valid)
      have firstRun:=Routine.repeat_iteration counter body store bit rest contents bodyTime middle
        (by simpa only [Routine.consume,contents,List.tail_cons] using bodyRun) bodyHalt
      have changed : middle.store=Routine.iteration counter transform store := bodyStore
      refine ⟨bodyTime+2+tailTime,by nlinarith,⟨finish,?_,tailHalt,?_⟩⟩
      · rw [Machine.run_add,firstRun,Option.bind_some,changed,tailRun]
      · rw [Function.iterate_succ_apply]
        exact tailStore

end Counting.StackMachine.EncodingPrograms
