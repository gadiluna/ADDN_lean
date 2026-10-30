import Counting.StackDagSuccessor
import Counting.StackDagHeader
import Counting.StackEncodingIncomingSpec

/-! Concrete semantic checks for a positive-level node and its selected
parent. Selection of the referenced node is a separate charged operation.
This module checks an actual parent index bound, level successor and leader
agreement; it is not merely a serialization recognizer. -/
namespace Counting.StackMachine.DagValidation
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

def positiveRoles : Fin 4 ↪ Fin 11:=⟨![0,6,7,9],by decide⟩
def rangeRoles : Fin 6 ↪ Fin 11:=⟨![0,1,6,7,8,9],by decide⟩
def levelRoles : Fin 7 ↪ Fin 11:=⟨![2,3,6,7,8,9,10],by decide⟩
def leaderRoles : Fin 6 ↪ Fin 11:=⟨![4,5,6,7,8,9],by decide⟩

def parentFieldsRoutine : Routine 9:=
  sequence (positivePreserving 7 positiveRoles)
    (sequence (leGuard 5 rangeRoles)
      (sequence (successorGuard 4 levelRoles) (equalityGuard 5 leaderRoles)))

def parentFieldsCheck (store : Store 9) : Bool:=
  ((lastPayloadBit false (store 0) && Binary.compareBits true (store 0) (store 1)) &&
    decide (Machine.increment (store 2)=store 3)) && decide (store 4=store 5)

def parentFieldsCost (store : Store 9) : Nat:=
  (6*(store 0).length+12)+1+((Binary.preservingCompareCost (store 0) (store 1)+4)+1+
    (successorCost (store 2) (store 3)+1+(Compare.preservingCost (store 4) (store 5)+4)))

theorem parentFields_executes (store : Store 9) (accepted : Bool) (tail : List Bool)
    (flag : store 6=accepted::tail) (empty : ∀ r : Fin 11,7≤r.val → store r=[]) :
    Executes parentFieldsRoutine store (parentFieldsCost store)
      (Function.update store 6 ((accepted && parentFieldsCheck store)::tail)) := by
  let p:=lastPayloadBit false (store 0)
  let b:=Binary.compareBits true (store 0) (store 1)
  let l:=decide (Machine.increment (store 2)=store 3)
  have positive:=positivePreserving_executes 7 positiveRoles store accepted tail flag
    (empty 7 (by decide)) (empty 9 (by decide))
  change Executes (positivePreserving 7 positiveRoles) store (6*(store 0).length+12)
    (Function.update store 6 ((accepted && p)::tail)) at positive
  let posStore:=Function.update store 6 ((accepted && p)::tail)
  have ranged:=leGuard_executes 5 rangeRoles posStore (accepted && p) tail
    (by simp [posStore,rangeRoles])
    (by simp [posStore,rangeRoles,empty 7 (by decide)])
    (by simp [posStore,rangeRoles,empty 8 (by decide)])
    (by simp [posStore,rangeRoles,empty 9 (by decide)])
  change Executes (leGuard 5 rangeRoles) posStore
    (Binary.preservingCompareCost (posStore 0) (posStore 1)+4)
    (Function.update posStore 6 (((accepted && p) &&
      Binary.compareBits true (posStore 0) (posStore 1))::tail)) at ranged
  simp [posStore] at ranged
  let rangeStore:=Function.update store 6 (((accepted && p) && b)::tail)
  have leveled:=successorGuard_executes 4 levelRoles rangeStore ((accepted && p) && b) tail
    (by simp [rangeStore,levelRoles]) (by
      intro i member
      fin_cases i <;> simp only [Finset.mem_insert,Finset.mem_singleton] at member
      all_goals first | contradiction | simp [rangeStore,levelRoles,empty])
  change Executes (successorGuard 4 levelRoles) rangeStore (successorCost (rangeStore 2) (rangeStore 3))
    (Function.update rangeStore 6 ((((accepted && p) && b) &&
      decide (Machine.increment (rangeStore 2)=rangeStore 3))::tail)) at leveled
  simp [rangeStore] at leveled
  let levelStore:=Function.update store 6 (((((accepted && p) && b) && l))::tail)
  have leaders:=equalityGuard_executes 5 leaderRoles levelStore ((((accepted && p) && b) && l)) tail
    (by simp [levelStore,leaderRoles])
    (by simp [levelStore,leaderRoles,empty 7 (by decide)])
    (by simp [levelStore,leaderRoles,empty 8 (by decide)])
    (by simp [levelStore,leaderRoles,empty 9 (by decide)])
  change Executes (equalityGuard 5 leaderRoles) levelStore
    (Compare.preservingCost (levelStore 4) (levelStore 5)+4)
    (Function.update levelStore 6 ((((((accepted && p) && b) && l)) &&
      decide (levelStore 4=levelStore 5))::tail)) at leaders
  simp [levelStore] at leaders
  have composed:=positive.sequence (ranged.sequence (leveled.sequence leaders))
  simpa [parentFieldsRoutine,parentFieldsCost,parentFieldsCheck,p,b,l,Bool.and_assoc] using composed

theorem parentFieldsCost_le (store : Store 9) :
    parentFieldsCost store≤100*((store 0).length+(store 1).length+(store 2).length+
      (store 3).length+(store 4).length+(store 5).length+1) := by
  have range:=Binary.preservingCompareCost_le (store 0) (store 1)
  have level:=successorCost_le (store 2) (store 3)
  have leader:=Compare.preservingCost_le (store 4) (store 5)
  unfold parentFieldsCost
  omega

def parentInput (index : Nat) (node parent : Executable.Node) : Store 9:=
  ![(parentCode node).bits,index.bits,parent.level.bits,node.level.bits,[parent.leader],[node.leader],[],[],[],[],[]]

def parentCondition (index : Nat) (node parent : Executable.Node) : Bool:=
  0<parentCode node && parentCode node ≤ index && parent.level+1==node.level && parent.leader==node.leader

theorem parentFieldsCheck_typed (index : Nat) (node parent : Executable.Node) :
    parentFieldsCheck (parentInput index node parent)=parentCondition index node parent := by
  have positive : lastPayloadBit false (parentCode node).bits=decide (0<parentCode node) := by
    apply Bool.eq_iff_iff.mpr
    rw [positivePayload_iff]
    simp only [Encoding.value_bits,decide_eq_true_eq]
    have canonical : canonicalPayload (parentCode node).bits=true :=
      (canonicalPayload_iff _).mpr (by rw [Encoding.value_bits])
    simp [canonical]
  have compared:=Binary.compareBits_le (parentCode node).bits index.bits
  simp only [Encoding.value_bits] at compared
  have comparison : Binary.compareBits true (parentCode node).bits index.bits=
      decide (parentCode node ≤ index) := by exact Bool.eq_iff_iff.mpr (by simpa using compared)
  change (((lastPayloadBit false (parentCode node).bits && Binary.compareBits true (parentCode node).bits index.bits) &&
    decide (Machine.increment parent.level.bits=node.level.bits)) && decide ([parent.leader]=[node.leader])) = parentCondition index node parent
  rw [positive,comparison,successor_naturals]
  apply Bool.eq_iff_iff.mpr
  simp [parentCondition]

/-- Exact extraction of the parent part of the existing validator. The
remaining factors are the incoming-edge checks and are not assumed here. -/
theorem nodeValid_parent_eq (vista : Executable.Vista) (index parent : Nat)
    (positive : (vista.node index).level≠0) (reference : (vista.node index).parent=some parent) :
    Executable.nodeValid vista index =
      (parentCondition index (vista.node index) (vista.node parent) &&
      Executable.countsSorted (vista.node index).incoming &&
      (vista.node index).incoming.all (fun edge => edge.1 < index &&
        (vista.node edge.1).level+1 == (vista.node index).level)) := by
  simp [Executable.nodeValid,parentCondition,parentCode,reference,positive]

end Counting.StackMachine.DagValidation
