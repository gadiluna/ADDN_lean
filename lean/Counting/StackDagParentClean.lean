import Counting.StackDagClean

/-! The concrete binary-parent check followed by charged workspace cleanup.
The current reference is consumed; the remaining current-node fields and
all caller registers are preserved. -/
namespace Counting.StackMachine.DagValidation
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

def parentReferenceClean : Routine 26:=sequence binaryParentCheck (clearRegisters redCleanupRegisters)

def parentCleanStore (store : Store 26) (accepted : Bool) (tail : List Bool)
    (values : List Executable.Node) (current : Nat) (node : Executable.Node) : Store 26:=
  Function.update (Function.update (Function.update store 22 []) 25 []) 1
    ((accepted && parentCheck values current node)::tail)

theorem parentReferenceClean_executes (store : Store 26) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀ r : Fin 28,r.val<17 → r≠1 → store r=[])
    (extraWork : ∀ r : Fin 28,r∈({18,19,20,26}:Finset (Fin 28)) → store r=[])
    (values : List Executable.Node) (current : Nat) (node : Executable.Node)
    (inside : current<values.length) (suffix : List Bool)
    (source : store 17=Encoding.sequence Encoding.node values++suffix)
    (level : store 21=node.level.bits) (reference : store 22=(parentCode node).bits)
    (leader : store 23=[node.leader]) (currentIndex : store 24=current.bits)
    (budget : (store 25).length=current) :
    ∃ time ≤ 10020*((store 17).length+(Encoding.node.encode node).length+1)^4,
      Executes parentReferenceClean store time (parentCleanStore store accepted tail values current node) := by
  obtain ⟨time,bounded,executed⟩:=binaryParentCheck_polynomial store accepted tail status work extraWork
    values current node inside suffix source level reference leader currentIndex budget
  let result:=binaryParentStore store accepted tail values current node inside
  let selected:=selectedParent values current node inside
  have count:=node_sequence_count_le values
  have indexBound : current≤(store 17).length:=by rw [source,List.length_append];omega
  have selectedLength : (Encoding.node.encode values[selected]).length≤(store 17).length:=by
    have member:=node_sequence_member_le values values[selected] (List.getElem_mem selected.isLt)
    rw [source,List.length_append]
    omega
  have metadata:=node_metadata_size_le values[selected]
  have currentMetadata:=node_metadata_size_le node
  have rest:=nodeSuffix_length_le values[selected]
  have registerBound (r : Fin 28) (member : r∈redCleanupRegisters) :
      (result r).length≤(store 17).length+(Encoding.node.encode node).length+1:=by
    simp only [redCleanupRegisters,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl
    · change values[selected].level.bits.length≤_
      rw [Encoding.bits_length]
      omega
    · change (parentCode values[selected]).bits.length≤_
      rw [Encoding.bits_length]
      omega
    · change 1≤_
      omega
    · change (List.replicate (min (parentCode node) (store 25).length-1) true).length≤_
      rw [List.length_replicate,budget]
      omega
    · change (nodeSuffix values[selected]).length≤_
      omega
    · change (store 22).length≤_
      rw [reference,Encoding.bits_length]
      omega
  obtain ⟨cleanupTime,cleanupBound,cleanupRun⟩:=clear_selected_executes redCleanupRegisters result
    ((store 17).length+(Encoding.node.encode node).length+1) registerBound
  have restored : clearedStore redCleanupRegisters result=parentCleanStore store accepted tail values current node:=by
    funext r
    fin_cases r <;> simp [clearedStore,redCleanupRegisters,result,binaryParentStore,parentCleanStore,
      lookupStore,prepareParentStore,work,extraWork]
  rw [restored] at cleanupRun
  have growth:=Nat.le_self_pow (by decide : 4≠0)
    ((store 17).length+(Encoding.node.encode node).length+1)
  change cleanupTime≤6*((store 17).length+(Encoding.node.encode node).length+1+2) at cleanupBound
  exact ⟨time+1+cleanupTime,by omega,executed.sequence cleanupRun⟩

end Counting.StackMachine.DagValidation
