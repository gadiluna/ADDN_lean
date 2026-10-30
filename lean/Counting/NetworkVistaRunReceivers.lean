import Counting.NetworkVistaRoundLoop

namespace Counting.StackMachine.NetworkVista
open Routine
set_option backward.isDefEq.respectTransparency false

/-- A receiver-loop bound with an explicit capacity for both the remaining
counter and emitted prefix. This allows a concrete body bound to depend on
the sizes of preserved caller fields, without quantifying over unbounded
arbitrary prefixes. -/
theorem receiverLoop_bounded_executes (extra : Nat) (roles : Fin 4 ↪ Fin (extra+2))
    (receiver : Routine extra) (base : Store extra) (views : List Executable.Vista)
    (counter index output : List Bool) (count : counter.length=views.length) (bound capacity : Nat)
    (counterBound : counter.length ≤ capacity)
    (totalBound : (Encoding.sequence Encoding.vista views).length+output.length ≤ capacity)
    (each : ∀ (done : Nat) (vista : Executable.Vista),views[done]?=some vista →
      ∀ (remaining emitted : List Bool),remaining.length ≤ capacity → emitted.length ≤ capacity →
        ∃ time  ≤  bound,Executes receiver
          (receiverFrame roles base remaining (List.replicate done true++index) emitted) time
          (Function.update (receiverFrame roles base remaining (List.replicate done true++index) emitted)
            (roles 3) (Encoding.vista.encode vista)))
    (lengthBound : ∀ vista∈views,(Encoding.vista.encode vista).length ≤ bound) :
    ∃ time  ≤  views.length*(3*bound+6)+1,
      Executes (receiverLoop extra roles receiver) (receiverFrame roles base counter index output) time
        (receiverFrame roles base [] (List.replicate views.length true++index)
          ((Encoding.sequence Encoding.vista views).reverse++output)) := by
  induction views generalizing counter index output with
  | nil =>
    have empty : counter=[] := List.length_eq_zero_iff.mp count
    obtain ⟨run,halt⟩ := repeat_empty (roles 0) (receiverBody extra roles receiver)
      (receiverFrame roles base counter index output) (by simp [receiverFrame,roles.injective.eq_iff,empty])
    refine ⟨1,by simp,⟨1,receiverFrame roles base counter index output⟩,run,halt,?_⟩
    simp [empty,Encoding.sequence]
  | cons vista views ih =>
    cases counter with
    | nil => simp at count
    | cons bit remaining =>
      have restBound : remaining.length ≤ capacity := by simp only [List.length_cons] at counterBound;omega
      have outBound : output.length ≤ capacity := by omega
      obtain ⟨t0,b0,body⟩ := each 0 vista (by simp) remaining output restBound outBound
      simp only [List.replicate_zero,List.nil_append] at body
      have first := receiverBody_executes extra roles receiver base remaining index output vista t0 body
      obtain ⟨finish0,run0,halt0,store0⟩ := first
      have nextEach : ∀ (done : Nat) (value : Executable.Vista),views[done]?=some value →
          ∀ (rest emitted : List Bool),rest.length ≤ capacity → emitted.length ≤ capacity →
            ∃ time  ≤  bound,Executes receiver
              (receiverFrame roles base rest (List.replicate done true++true::index) emitted) time
              (Function.update (receiverFrame roles base rest (List.replicate done true++true::index) emitted)
                (roles 3) (Encoding.vista.encode value)) := by
        intro done value lookup rest emitted br be
        simpa only [List.replicate_succ',List.append_assoc,List.singleton_append] using
          each (done+1) value (by simpa using lookup) rest emitted br be
      have tailBound : (Encoding.sequence Encoding.vista views).length+
          ((Encoding.vista.encode vista).reverse++output).length ≤ capacity := by
        simp only [Encoding.sequence,List.length_append] at totalBound
        simp only [List.length_append,List.length_reverse]
        omega
      obtain ⟨t1,b1,finish1,run1,halt1,store1⟩ := ih remaining (true::index)
        ((Encoding.vista.encode vista).reverse++output) (by simpa using count) restBound tailBound nextEach
        (fun value member=>lengthBound value (List.mem_cons_of_mem vista member))
      have atCounter : receiverFrame roles base (bit::remaining) index output (roles 0)=bit::remaining := by
        simp [receiverFrame,roles.injective.eq_iff]
      have consumed : Function.update (receiverFrame roles base (bit::remaining) index output) (roles 0) remaining=
          receiverFrame roles base remaining index output := by
        funext r
        by_cases r0:r=roles 0 <;> by_cases r1:r=roles 1 <;>
          by_cases r2:r=roles 2 <;> by_cases r3:r=roles 3 <;>
          simp [receiverFrame,r0,r1,r2,r3,roles.injective.eq_iff]
      have firstRun := repeat_iteration (roles 0) (receiverBody extra roles receiver)
        (receiverFrame roles base (bit::remaining) index output) bit remaining atCounter
        (t0+2*(Encoding.vista.encode vista).length+4) finish0 (by simpa only [consumed] using run0) halt0
      have firstRun' : Machine.run (step (receiverLoop extra roles receiver).program)
          (t0+2*(Encoding.vista.encode vista).length+4+2)
          ⟨0,receiverFrame roles base (bit::remaining) index output⟩=some ⟨0,finish0.store⟩ := firstRun
      refine ⟨t0+2*(Encoding.vista.encode vista).length+4+2+t1,?_,finish1,?_,halt1,?_⟩
      · have sized := lengthBound vista List.mem_cons_self
        simp only [List.length_cons];nlinarith
      · rw [Machine.run_add,firstRun',Option.bind_some,store0]
        exact run1
      · simpa only [List.length_cons,List.replicate_succ',List.append_assoc,List.singleton_append,
          Encoding.sequence,List.reverse_append] using store1

end Counting.StackMachine.NetworkVista
