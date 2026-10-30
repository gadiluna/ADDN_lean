import Counting.StackDagRedBounds
import Counting.StackRoutineClean

namespace Counting.StackMachine.DagValidation
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

/-- The cleanup cost depends only on the registers actually cleared;
large preserved caller data does not affect the running time. -/
theorem clear_selected_executes {registers : Nat} (selected : List (Fin (registers+2)))
    (store : Store registers) (bound : Nat)
    (bounded : ∀ r∈selected,(store r).length≤bound) :
    ∃ time ≤ selected.length*(bound+2),
      Executes (clearRegisters selected) store time (clearedStore selected store) := by
  induction selected generalizing store with
  | nil=>exact ⟨0,by simp,skip_executes store⟩
  | cons r rest ih=>
    have nextBound (j : Fin (registers+2)) (inside : j∈rest) :
        ((Function.update store r []) j).length≤bound := by
      by_cases same : j=r
      · subst j;simp
      · simpa only [Function.update_of_ne same] using bounded j (by simp [inside])
    obtain ⟨time,timeBound,tail⟩:=ih (Function.update store r []) nextBound
    have result : clearedStore rest (Function.update store r [])=clearedStore (r::rest) store := by
      funext j
      by_cases same : j=r <;> by_cases inside : j∈rest <;>
        simp [clearedStore,same,inside]
    rw [result] at tail
    refine ⟨_,?_,(clear_executes r store).sequence tail⟩
    have headBound:=bounded r (by simp)
    simp only [List.length_cons]
    nlinarith

theorem nodeSuffix_length_le (node : Executable.Node) :
    (nodeSuffix node).length≤(Encoding.node.encode node).length := by
  change (Encoding.natural.encode node.degree++
    (Encoding.list (Encoding.product Encoding.natural Encoding.natural)).encode node.incoming).length≤
    (Encoding.natural.encode node.level++(Encoding.optionalNatural.encode node.parent++
      ([node.leader]++(Encoding.natural.encode node.degree++
        (Encoding.list (Encoding.product Encoding.natural Encoding.natural)).encode node.incoming)))).length
  simp only [List.length_append,List.length_cons,List.length_nil]
  omega

def redCleanupRegisters : List (Fin 28):=[0,2,3,18,19,22]
def redReferenceClean : Routine 26:=sequence redReferenceCheck (clearRegisters redCleanupRegisters)

def redCleanStore (store : Store 26) (accepted : Bool) (tail : List Bool)
    (values : List Executable.Node) (current targetLevel sourceIndex : Nat) : Store 26:=
  Function.update (Function.update (Function.update store 22 []) 25 []) 1
    ((accepted && redCondition values current targetLevel sourceIndex)::tail)

theorem redReferenceClean_executes (store : Store 26) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀ r : Fin 28,r.val<17 → r≠1 → store r=[])
    (extraWork : ∀ r : Fin 28,r∈({18,19,20,26}:Finset (Fin 28)) → store r=[])
    (values : List Executable.Node) (current targetLevel sourceIndex : Nat)
    (inside : current<values.length) (suffix : List Bool)
    (source : store 17=Encoding.sequence Encoding.node values++suffix)
    (level : store 21=targetLevel.bits) (reference : store 22=sourceIndex.bits)
    (budget : (store 25).length=current) :
    ∃ time ≤ 20020*((store 17).length+sourceIndex.size+targetLevel.size+1)^4,
      Executes redReferenceClean store time (redCleanStore store accepted tail values current targetLevel sourceIndex) := by
  obtain ⟨time,bounded,executed⟩:=redReferenceCheck_polynomial store accepted tail status work extraWork
    values current targetLevel sourceIndex inside suffix source level reference budget
  let result:=redReferenceStore store accepted tail values current targetLevel sourceIndex inside
  let selected:=selectedRed values current sourceIndex inside
  have count:=node_sequence_count_le values
  have indexBound : current≤(store 17).length:=by rw [source,List.length_append];omega
  have selectedLength : (Encoding.node.encode values[selected]).length≤(store 17).length := by
    have member:=node_sequence_member_le values values[selected] (List.getElem_mem selected.isLt)
    rw [source,List.length_append]
    omega
  have metadata:=node_metadata_size_le values[selected]
  have rest:=nodeSuffix_length_le values[selected]
  have successorSize : (sourceIndex+1).size ≤ sourceIndex.size+1 := by
    have length:=increment_length_le sourceIndex.bits
    simpa only [Machine.increment_bits,Encoding.bits_length] using length
  have registerBound (r : Fin 28) (member : r∈redCleanupRegisters) :
      (result r).length≤(store 17).length+sourceIndex.size+1 := by
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
    · change (List.replicate (min (sourceIndex+1) (store 25).length-1) true).length≤_
      rw [List.length_replicate,budget]
      omega
    · change (nodeSuffix values[selected]).length≤_
      omega
    · change (sourceIndex+1).bits.length≤_
      rw [Encoding.bits_length]
      omega
  obtain ⟨cleanupTime,cleanupBound,cleanupRun⟩:=clear_selected_executes redCleanupRegisters result
    ((store 17).length+sourceIndex.size+1) registerBound
  have restored : clearedStore redCleanupRegisters result=redCleanStore store accepted tail values current targetLevel sourceIndex := by
    funext r
    fin_cases r <;> simp [clearedStore,redCleanupRegisters,result,redReferenceStore,redCleanStore,
      lookupStore,prepareParentStore,work,extraWork]
  rw [restored] at cleanupRun
  have growth:=Nat.le_self_pow (by decide : 4≠0)
    ((store 17).length+sourceIndex.size+targetLevel.size+1)
  change cleanupTime≤6*((store 17).length+sourceIndex.size+1+2) at cleanupBound
  exact ⟨time+1+cleanupTime,by omega,executed.sequence cleanupRun⟩

end Counting.StackMachine.DagValidation
