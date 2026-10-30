import Counting.StackLoop

namespace Counting.StackMachine.Routine

/-- A routine starts in control zero and halts after exactly the stated
number of stack transitions, producing the whole specified register file. -/
def Executes {registers : Nat} (routine : Routine registers)
    (initial : Store registers) (steps : Nat) (result : Store registers) : Prop :=
  ∃ finish : Config routine.program,
    Machine.run (step routine.program) steps ⟨0,initial⟩ = some finish ∧
      step routine.program finish = none ∧ finish.store = result

theorem Executes.sequence {registers : Nat} {first second : Routine registers}
    {initial middle result : Store registers} {firstSteps secondSteps : Nat}
    (firstRun : Executes first initial firstSteps middle)
    (secondRun : Executes second middle secondSteps result) :
    Executes (sequence first second) initial (firstSteps+1+secondSteps) result := by
  obtain ⟨firstFinal,ranFirst,haltFirst,firstStore⟩ := firstRun
  obtain ⟨secondFinal,ranSecond,haltSecond,secondStore⟩ := secondRun
  refine ⟨rightConfig first second secondFinal,?_,?_,secondStore⟩
  · exact sequence_run first second firstSteps secondSteps initial firstFinal secondFinal
      ranFirst haltFirst (firstStore ▸ ranSecond)
  · rw [right_step,haltSecond]
    rfl

def consume {registers : Nat} (counter : Fin (registers+2)) (store : Store registers) : Store registers :=
  Function.update store counter (store counter).tail

def iteration {registers : Nat} (counter : Fin (registers+2))
    (body : Store registers → Store registers) (store : Store registers) : Store registers :=
  body (consume counter store)

def loopTime {registers : Nat} (counter : Fin (registers+2))
    (body : Store registers → Store registers) (cost : Store registers → Nat) : Nat → Store registers → Nat
  | 0, _ => 1
  | count+1, store => cost (consume counter store)+2+loopTime counter body cost count (iteration counter body store)

theorem forEach_executes {registers : Nat} (counter : Fin (registers+2)) (routine : Routine registers)
    (body : Store registers → Store registers) (cost : Store registers → Nat)
    (executes : ∀ store, Executes routine store (cost store) (body store))
    (preserves : ∀ store, body store counter = store counter)
    (count : Nat) (store : Store registers) (length : (store counter).length = count) :
    Executes (forEach counter routine) store (loopTime counter body cost count store)
      ((iteration counter body)^[count] store) := by
  induction count generalizing store with
  | zero =>
      have empty : store counter = [] := List.length_eq_zero_iff.mp length
      obtain ⟨ran,halted⟩ := repeat_empty counter routine store empty
      exact ⟨⟨1,store⟩,ran,halted,rfl⟩
  | succ count ih =>
      cases contents : store counter with
      | nil => simp only [contents,List.length_nil] at length; omega
      | cons bit rest =>
          obtain ⟨middle,bodyRun,bodyHalt,bodyStore⟩ := executes (consume counter store)
          have nextLength : ((iteration counter body store) counter).length = count := by
            simp only [iteration,preserves,consume,Function.update_self,contents,List.tail_cons]
            simp only [contents,List.length_cons] at length
            omega
          obtain ⟨finish,tailRun,tailHalt,tailStore⟩ := ih (iteration counter body store) nextLength
          have firstRun := repeat_iteration counter routine store bit rest contents
            (cost (consume counter store)) middle (by simpa only [consume,contents,List.tail_cons] using bodyRun) bodyHalt
          have changed : middle.store = iteration counter body store := bodyStore
          refine ⟨finish,?_,tailHalt,?_⟩
          · change Machine.run (step (forEach counter routine).program)
              ((cost (consume counter store)+2)+loopTime counter body cost count (iteration counter body store)) _ = _
            rw [Machine.run_add,firstRun,Option.bind_some,changed,tailRun]
          · rw [Function.iterate_succ_apply]
            exact tailStore

/-- A bounded invariant supplies a uniform body bound for all iterations;
the loop pays exactly one final empty pop in addition to its iterations. -/
theorem loopTime_le {registers : Nat} (counter : Fin (registers+2))
    (body : Store registers → Store registers) (cost : Store registers → Nat)
    (invariant : Store registers → Prop) (bodyBound : Nat)
    (preserved : ∀ store, invariant store → invariant (iteration counter body store))
    (bounded : ∀ store, invariant store → cost (consume counter store) ≤ bodyBound)
    (count : Nat) (store : Store registers) (valid : invariant store) :
    loopTime counter body cost count store ≤ count*(bodyBound+2)+1 := by
  induction count generalizing store with
  | zero => simp only [loopTime,Nat.zero_mul,Nat.zero_add,le_refl]
  | succ count ih =>
      have next := ih (iteration counter body store) (preserved store valid)
      have current := bounded store valid
      simp only [loopTime]
      nlinarith

end Counting.StackMachine.Routine
