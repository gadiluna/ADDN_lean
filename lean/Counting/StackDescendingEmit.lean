import Counting.StackRoutineBoundedLoop

namespace Counting.StackMachine.Routine

def emitBody {registers : Nat} (counter output : Fin (registers+2)) (chunk : Nat → List Bool)
    (store : Store registers) : Store registers :=
  Function.update store output (chunk (store counter).length++store output)

def emittedChunks (chunk : Nat → List Bool) (count : Nat) : List Bool :=
  (List.range count).flatMap chunk

theorem emittedChunks_succ (chunk : Nat → List Bool) (count : Nat) :
    emittedChunks chunk (count+1) = emittedChunks chunk count++chunk count := by
  simp only [emittedChunks,List.range_succ,List.flatMap_append,List.flatMap_singleton]

/-- Descending counter traversal combined with prefix emission produces
ascending index order. The entire register file is characterized. -/
theorem iterate_emitBody {registers : Nat} (counter output : Fin (registers+2)) (distinct : counter ≠ output)
    (chunk : Nat → List Bool) (count : Nat) (store : Store registers) (length : (store counter).length=count) :
    (iteration counter (emitBody counter output chunk))^[count] store =
      Function.update (Function.update store counter []) output (emittedChunks chunk count++store output) := by
  induction count generalizing store with
  | zero =>
      have empty : store counter=[] := List.length_eq_zero_iff.mp length
      simp only [Function.iterate_zero,Function.id_def,emittedChunks,List.range_zero,List.flatMap_nil,List.nil_append]
      rw [← empty,Function.update_eq_self,Function.update_eq_self]
  | succ count ih =>
      cases contents : store counter with
      | nil => simp only [contents,List.length_nil] at length; omega
      | cons bit rest =>
          have restLength : rest.length=count := by simp only [contents,List.length_cons] at length; omega
          let next := iteration counter (emitBody counter output chunk) store
          have nextCounter : next counter=rest := by
            simp [next,iteration,emitBody,consume,distinct,contents]
          have nextOutput : next output=chunk count++store output := by
            simp [next,iteration,emitBody,consume,Ne.symm distinct,contents,restLength]
          rw [Function.iterate_succ_apply,ih next (by rw [nextCounter,restLength])]
          funext register
          by_cases isOutput : register=output
          · subst register
            simp only [Function.update_self,nextOutput,emittedChunks_succ,List.append_assoc]
          · by_cases isCounter : register=counter
            · subst register
              simp [distinct]
            · simp [Function.update_of_ne isOutput,Function.update_of_ne isCounter,next,iteration,emitBody,consume]

/-- A genuine routine that emits one index-dependent chunk can be looped
without adding a free iterator or a free concatenation operation. -/
theorem descendingEmit_executes {registers : Nat} (counter output : Fin (registers+2))
    (distinct : counter ≠ output) (routine : Routine registers) (chunk : Nat → List Bool)
    (invariant : Store registers → Prop) (bodyBound : Nat)
    (bodyExecutes : ∀ store, invariant store → ∃ time ≤ bodyBound,
      Executes routine store time (emitBody counter output chunk store))
    (consumeInvariant : ∀ store, invariant store → invariant (consume counter store))
    (emitInvariant : ∀ store, invariant store → invariant (emitBody counter output chunk store))
    (store : Store registers) (valid : invariant store) :
    ∃ transitions ≤ (store counter).length*(bodyBound+2)+1,
      Executes (forEach counter routine) store transitions
        (Function.update (Function.update store counter []) output
          (emittedChunks chunk (store counter).length++store output)) := by
  obtain ⟨time,bounded,executed⟩ := forEach_bounded counter routine (emitBody counter output chunk) invariant bodyBound
    bodyExecutes (fun store _ => by simp [emitBody,distinct]) consumeInvariant emitInvariant
    (store counter).length store valid rfl
  rw [iterate_emitBody counter output distinct chunk _ store rfl] at executed
  exact ⟨time,bounded,executed⟩

end Counting.StackMachine.Routine
