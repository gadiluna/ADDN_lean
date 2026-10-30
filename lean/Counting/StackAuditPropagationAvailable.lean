import Counting.StackAuditPropagationAssignCurrent
import Counting.StackDagEmptyGuard

namespace Counting.StackMachine.AuditPropagation
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

abbrev assignAvailable : Routine 35 := sequence (DagValidation.emptyFlag 36 31)
  (branchRoutine 31 (skip 35) assignCurrent)

def availableValues : List Nat → List Nat
  | [] => []
  | _::values => values

def availableWeights (weights : Array Nat) (index : Nat) : List Nat → Array Nat
  | [] => weights
  | value::_ => weights.setIfInBounds index value

/-- An exhausted value stream is detected without decoding a nonexistent
field. Thus this routine implements the exact truncation behavior of zip. -/
theorem assignAvailable_executes (store : Store 35) (weights : Array Nat) (index : Nat)
    (inside : index<weights.size) (values : List Nat)
    (source : store 36=Encoding.sequence Encoding.natural values)
    (array : store 35=(Encoding.array Encoding.natural).encode weights)
    (counter : store 18=List.replicate index true)
    (e2 : store 2=[]) (e3 : store 3=[]) (e4 : store 4=[]) (e21 : store 21=[]) (e31 : store 31=[]) :
    ∃ time ≤ 5*(store 35).length+8*index+22*(store 36).length+40,
      Executes assignAvailable store time
        (Function.update (Function.update store 36 (Encoding.sequence Encoding.natural (availableValues values))) 35
          ((Encoding.array Encoding.natural).encode (availableWeights weights index values))) := by
  have checked := DagValidation.emptyFlag_executes (36:Fin 37) 31 store
  cases values with
  | nil =>
    have empty : store 36=[] := source
    simp only [empty,decide_true,e31] at checked
    let flagged := Function.update store 31 [true]
    have restored : Function.update flagged 31 []=store := by
      simp only [flagged,Function.update_idem]
      rw [←e31,Function.update_eq_self]
    have skipped : Executes (skip 35) (Function.update flagged 31 []) 0 store := by
      rw [restored];exact skip_executes store
    have branched := branch_executes_true (31:Fin 37) (skip 35) assignCurrent flagged store [] 0
      (by simp [flagged]) skipped
    have finish : Function.update (Function.update store 36 (Encoding.sequence Encoding.natural (availableValues []))) 35
        ((Encoding.array Encoding.natural).encode (availableWeights weights index []))=store := by
      simp only [availableValues,availableWeights,Encoding.sequence]
      rw [←empty,Function.update_eq_self,←array,Function.update_eq_self]
    rw [finish]
    refine ⟨_,?_,checked.sequence branched⟩
    simp only [DagValidation.emptyFlagCost,empty,if_true]
    omega
  | cons value values =>
    have nonempty : store 36≠[] := by
      intro equal
      have positive : 0<(Encoding.natural.encode value).length := by rw [Encoding.natural_length];omega
      have lengthEq := congrArg List.length source
      simp only [equal,Encoding.sequence,List.length_nil,List.length_append] at lengthEq
      omega
    simp only [nonempty,decide_false,e31] at checked
    let flagged := Function.update store 31 [false]
    have restored : Function.update flagged 31 []=store := by
      simp only [flagged,Function.update_idem]
      rw [←e31,Function.update_eq_self]
    obtain ⟨time,bounded,assigned⟩ := assignCurrent_executes store weights index value inside
      (Encoding.sequence Encoding.natural values) source array counter e2 e3 e4 e21 e31
    have assignedReady : Executes assignCurrent (Function.update flagged 31 []) time
        (Function.update (Function.update store 36 (Encoding.sequence Encoding.natural values)) 35
          ((Encoding.array Encoding.natural).encode (weights.setIfInBounds index value))) := by
      rw [restored];exact assigned
    have branched := branch_executes_false (31:Fin 37) (skip 35) assignCurrent flagged _ [] time
      (by simp [flagged]) assignedReady
    refine ⟨_,?_,checked.sequence branched⟩
    have valueBound : value.size ≤ (store 36).length := by
      rw [source,Encoding.sequence,List.length_append,Encoding.natural_length];omega
    simp only [DagValidation.emptyFlagCost,nonempty,if_false]
    omega

end Counting.StackMachine.AuditPropagation
