import Counting.StackBooleanFold

namespace Counting.StackMachine.BooleanFold
open Routine

abbrev prefixRoutine {registers : Nat} (kind : Kind) (source accumulator counter : Fin (registers+2)) :=
  forEach counter (single kind source accumulator)

def prefixStore {registers : Nat} (source accumulator counter : Fin (registers+2))
    (store : Store registers) (suffix : List Bool) (value : Bool) (tail : List Bool) :=
  Function.update (Function.update (Function.update store source suffix) counter []) accumulator (value::tail)

/-- The counter bounds the inspected prefix. The uninspected suffix and all
unrelated registers survive even when the accumulator is already false. -/
theorem prefix_executes (kind : Kind) (source accumulator counter : Fin (registers+2))
    (sourceAccumulator : source ≠ accumulator) (sourceCounter : source ≠ counter)
    (accumulatorCounter : accumulator ≠ counter) (store : Store registers)
    (bits suffix : List Bool) (value : Bool) (tail : List Bool)
    (contents : store source=bits++suffix) (accumulated : store accumulator=value::tail)
    (counted : store counter=List.replicate bits.length true) :
    Executes (prefixRoutine kind source accumulator counter) store (5*bits.length+1)
      (prefixStore source accumulator counter store suffix (bits.foldl (operation kind) value) tail) := by
  induction bits generalizing store value with
  | nil =>
      have empty : store counter=[] := by simpa only [List.length_nil,List.replicate_zero] using counted
      have same : prefixStore source accumulator counter store suffix value tail=store := by
        simp only [List.nil_append] at contents
        simp [prefixStore,←contents,←accumulated,←empty,Function.update_eq_self]
      obtain ⟨ran,halted⟩ := repeat_empty counter (single kind source accumulator) store empty
      exact ⟨⟨1,store⟩,ran,halted,same.symm⟩
  | cons bit rest ih =>
      let count := List.replicate rest.length true
      let consumed := Function.update store counter count
      let next := updated source accumulator consumed (rest++suffix) (operation kind value bit) tail
      have sourceAfter : consumed source=bit::(rest++suffix) := by
        simp only [consumed,Function.update_of_ne sourceCounter,contents,List.cons_append]
      have accumulatorAfter : consumed accumulator=value::tail := by
        simp only [consumed,Function.update_of_ne accumulatorCounter,accumulated]
      obtain ⟨bodyFinish,bodyRan,bodyHalted,bodyResult⟩ := single_executes kind source accumulator
        sourceAccumulator consumed bit value (rest++suffix) tail sourceAfter accumulatorAfter
      have counterValue : store counter=true::count := by
        simpa only [List.length_cons,List.replicate_succ,count] using counted
      have firstRun := repeat_iteration counter (single kind source accumulator) store true count counterValue
        3 bodyFinish bodyRan bodyHalted
      have nextSource : next source=rest++suffix := by simp [next,updated,sourceAccumulator]
      have nextAccumulator : next accumulator=operation kind value bit::tail := by simp [next,updated]
      have nextCounter : next counter=count := by
        simp [next,updated,consumed,sourceCounter.symm,accumulatorCounter.symm]
      obtain ⟨finish,ran,halted,result⟩ := ih next (operation kind value bit) nextSource nextAccumulator nextCounter
      refine ⟨finish,?_,halted,?_⟩
      · rw [List.length_cons,show 5*(rest.length+1)+1=(3+2)+(5*rest.length+1) by omega,
          Machine.run_add,firstRun,Option.bind_some,bodyResult]
        exact ran
      · rw [result]
        simp only [List.foldl_cons,prefixStore,next,updated,consumed]
        funext r
        by_cases atSource : r=source
        · subst r; simp [sourceAccumulator,sourceCounter]
        · by_cases atAccumulator : r=accumulator
          · subst r; simp
          · by_cases atCounter : r=counter
            · subst r; simp [accumulatorCounter.symm]
            · simp [Function.update_of_ne,atSource,atAccumulator,atCounter]

/-- Marker-table validation used by the SAT verifier. -/
theorem markers_executes (source accumulator counter : Fin (registers+2))
    (sourceAccumulator : source ≠ accumulator) (sourceCounter : source ≠ counter)
    (accumulatorCounter : accumulator ≠ counter) (store : Store registers)
    (markers suffix : List Bool) (accepted : Bool) (tail : List Bool)
    (contents : store source=markers++suffix) (accumulated : store accumulator=accepted::tail)
    (counted : store counter=List.replicate markers.length true) :
    Executes (prefixRoutine .conjunction source accumulator counter) store (5*markers.length+1)
      (prefixStore source accumulator counter store suffix (accepted && markers.all id) tail) := by
  simpa only [fold_conjunction] using prefix_executes .conjunction source accumulator counter
    sourceAccumulator sourceCounter accumulatorCounter store markers suffix accepted tail contents accumulated counted

end Counting.StackMachine.BooleanFold
