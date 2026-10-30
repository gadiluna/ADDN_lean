import Counting.StackRoutineBasic
import Counting.StackRoutineLists
import Counting.EncodingDag

namespace Counting.StackMachine.NetworkVista
open Routine
set_option backward.isDefEq.respectTransparency false

/-- Counter, receiver index, reversed new configuration and fresh-vista
output. Every other register retains the preceding round's configuration. -/
def receiverFrame {registers : Nat} (roles : Fin 4 ↪ Fin (registers+2))
    (base : Store registers) (counter index output : List Bool) : Store registers :=
  Function.update (Function.update (Function.update (Function.update base (roles 0) counter)
    (roles 1) index) (roles 2) output) (roles 3) []

def receiverBody (extra : Nat) (roles : Fin 4 ↪ Fin (extra+2)) (receiver : Routine extra) : Routine extra :=
  sequence receiver (sequence
    (ofProgram (ListPrograms.reverseProgram extra (roles 3) (roles 2)))
    (pushBit (roles 1) true))

def receiverLoop (extra : Nat) (roles : Fin 4 ↪ Fin (extra+2)) (receiver : Routine extra) : Routine extra :=
  forEach (roles 0) (receiverBody extra roles receiver)

/-- Physical assembly of one receiver's encoded DAG into a separate new
configuration. The old configuration stays in the unmodified base fields. -/
theorem receiverBody_executes (extra : Nat) (roles : Fin 4 ↪ Fin (extra+2))
    (receiver : Routine extra) (base : Store extra) (counter index output : List Bool)
    (vista : Executable.Vista) (time : Nat)
    (run : Executes receiver (receiverFrame roles base counter index output) time
      (Function.update (receiverFrame roles base counter index output) (roles 3) (Encoding.vista.encode vista))) :
    Executes (receiverBody extra roles receiver) (receiverFrame roles base counter index output)
      (time+2*(Encoding.vista.encode vista).length+4)
      (receiverFrame roles base counter (true::index) ((Encoding.vista.encode vista).reverse++output)) := by
  let middle := Function.update (receiverFrame roles base counter index output) (roles 3) (Encoding.vista.encode vista)
  have reverse := reverse_executes extra (roles 3) (roles 2) (by intro eq;have := roles.injective eq;contradiction) middle
  rw [show middle (roles 3)=Encoding.vista.encode vista by simp [middle],
    show middle (roles 2)=output by simp [middle,receiverFrame,roles.injective.eq_iff]] at reverse
  let reversed := Function.update (Function.update middle (roles 3) [])
    (roles 2) ((Encoding.vista.encode vista).reverse++output)
  have push := pushBit_executes (roles 1) true reversed
  have final : Function.update reversed (roles 1) (true::reversed (roles 1))=
      receiverFrame roles base counter (true::index) ((Encoding.vista.encode vista).reverse++output) := by
    funext r
    by_cases r0:r=roles 0 <;> by_cases r1:r=roles 1 <;> by_cases r2:r=roles 2 <;> by_cases r3:r=roles 3 <;>
      simp_all [reversed,middle,receiverFrame,roles.injective.eq_iff]
  rw [final] at push
  have joined := run.sequence (reverse.sequence push)
  convert joined using 1 <;> first | rfl | omega

/-- A finite receiver traversal with an actual reverse-and-append body.
The caller supplies the proved receiver routine; the loop itself accounts
for every stack transition, consumes exactly one entry per agent, and never
replaces the old configuration during a round. -/
theorem receiverLoop_executes (extra : Nat) (roles : Fin 4 ↪ Fin (extra+2))
    (receiver : Routine extra) (base : Store extra) (views : List Executable.Vista)
    (counter index output : List Bool) (count : counter.length=views.length) (bound : Nat)
    (each : ∀ (done : Nat) (vista : Executable.Vista), views[done]?=some vista →
      ∀ (remaining emitted : List Bool),
        ∃ time ≤ bound, Executes receiver
          (receiverFrame roles base remaining (List.replicate done true++index) emitted) time
          (Function.update (receiverFrame roles base remaining (List.replicate done true++index) emitted)
            (roles 3) (Encoding.vista.encode vista)))
    (lengthBound : ∀vista∈views,(Encoding.vista.encode vista).length≤bound) :
    ∃ time ≤ views.length*(3*bound+6)+1,
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
      obtain ⟨t0,b0,body⟩ := each 0 vista (by simp) remaining output
      simp only [List.replicate_zero,List.nil_append] at body
      have first := receiverBody_executes extra roles receiver base remaining index output vista t0 body
      obtain ⟨finish0,run0,halt0,store0⟩ := first
      have nextEach : ∀ (done : Nat) (value : Executable.Vista), views[done]?=some value →
          ∀ (rest emitted : List Bool), ∃ time ≤ bound, Executes receiver
          (receiverFrame roles base rest (List.replicate done true++true::index) emitted) time
          (Function.update (receiverFrame roles base rest (List.replicate done true++true::index) emitted)
            (roles 3) (Encoding.vista.encode value)) := by
        intro done value lookup rest emitted
        simpa only [List.replicate_succ',List.append_assoc,List.singleton_append] using
          each (done+1) value (by simpa using lookup) rest emitted
      obtain ⟨t1,b1,finish1,run1,halt1,store1⟩ := ih remaining (true::index)
        ((Encoding.vista.encode vista).reverse++output) (by simpa using count) nextEach
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
