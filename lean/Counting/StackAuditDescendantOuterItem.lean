import Counting.StackAuditDescendantOuterSelection
import Counting.StackRoutineMove
import Counting.StackDagIncrement

namespace Counting.StackMachine.AuditDescendant
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

def accumulateAdvance : Routine 46 := sequence (move 45 35 45 0)
  (sequence (ofProgram (combineFlagsProgram 46 45))
    (sequence (DagValidation.incrementRoutine 45 0 29 1) (pushBit 43 true)))

theorem accumulateAdvance_executes (store : Store 46) (index : Nat) (accepted hit : Bool)
    (tail : List Bool) (flag : store 35=[hit]) (accumulator : store 45=accepted::tail)
    (current : store 29=(index+1).bits) (e0 : store 0=[]) (e1 : store 1=[]) :
    ∃ time ≤ 4*(index+1).size+25,
      Executes accumulateAdvance store time
        (Function.update (Function.update (Function.update (Function.update store 35 [])
          45 ((accepted && hit)::tail)) 29 (index+1+1).bits) 43 (true::store 43)) := by
  have a:=move_executes 45 (35:Fin 48) 45 0 (by decide) (by decide) (by decide) store e0
  rw [flag,accumulator] at a
  let moved:=Function.update (Function.update store 35 []) 45 (hit::accepted::tail)
  have movedEq : Function.update (Function.update store 45 ([hit] ++ accepted::tail)) 35 []=moved := by
    funext r
    by_cases r35 : r=35 <;> by_cases r45 : r=45 <;> simp [moved,r35,r45]
  rw [movedEq] at a
  have b:=combineFlags_executes 46 (45:Fin 48) moved accepted hit tail (by simp [moved])
  let combined:=Function.update (Function.update store 35 []) 45 ((accepted && hit)::tail)
  have same : Function.update moved 45 ((accepted && hit)::tail)=combined := by simp [moved,combined]
  rw [same] at b
  obtain ⟨time,bound,c⟩:=DagValidation.increment_natural 45 (0:Fin 48) 29 1
    (by decide) (by decide) (by decide) combined
    (by simp [combined,e0]) (by simp [combined,e1]) (index+1) (by simp [combined,current])
  let advanced:=Function.update combined 29 (index+1+1).bits
  have d:=pushBit_executes (43:Fin 48) true advanced
  have indexAt : advanced 43=store 43 := by simp [advanced,combined]
  rw [indexAt] at d
  refine ⟨_,?_,a.sequence (b.sequence (c.sequence d))⟩
  simp only [List.length_cons,List.length_nil]
  omega

def outerItem : Routine 46 := sequence checkSelected accumulateAdvance

def outerItemResult (store : Store 46) (index : Nat) (accepted hit : Bool) (tail : List Bool) : Store 46 :=
  Function.update (Function.update (Function.update store 45 ((accepted && hit)::tail))
    29 (index+1+1).bits) 43 (true::store 43)

theorem outerItem_executes (store : Store 46) (vista : Executable.Vista)
    (weights : Array Nat) (anchor last : Nat) (index : Fin vista.nodes.size) (steps : List Bool)
    (stepCount : steps.length=last-anchor) (accepted : Bool) (tail : List Bool)
    (source : store 46=(Encoding.array Encoding.node).encode vista.nodes)
    (weightsAt : store 32=(Encoding.array Encoding.natural).encode weights)
    (indexAt : (store 43).length=index.val) (anchorAt : store 40=anchor.bits)
    (lastAt : store 34=last.bits) (target : store 29=(index.val+1).bits)
    (stepBudget : store 38=steps) (accumulator : store 45=accepted::tail)
    (empty : ∀ r : Fin 48,r.val<40 → r≠29 → r≠32 → r≠34 → r≠38 → store r=[]) :
    ∃ time ≤ 82000000000000*((store 46).length+(store 32).length+steps.length+anchor.size+last.size+1)^6,
      Executes outerItem store time
        (outerItemResult store index.val accepted
          (Executable.auditAncestor vista weights anchor last index.val) tail) := by
  obtain ⟨checkTime,checkBound,a⟩:=checkSelected_executes store vista weights anchor last index steps stepCount
    source weightsAt indexAt anchorAt lastAt target stepBudget empty
  let hit:=Executable.auditAncestor vista weights anchor last index.val
  let checked:=Function.update store 35 [hit]
  obtain ⟨advanceTime,advanceBound,b⟩:=accumulateAdvance_executes checked index.val accepted hit tail
    (by simp [checked]) (by simp [checked,accumulator]) (by simp [checked,target])
    (by simp [checked,empty]) (by simp [checked,empty])
  have restored : Function.update checked 35 []=store := by
    simp only [checked,Function.update_idem]
    rw [←empty 35 (by decide) (by decide) (by decide) (by decide) (by decide),Function.update_eq_self]
  rw [restored] at b
  have unchanged : checked 43=store 43 := by simp [checked]
  rw [unchanged] at b
  have nodes : vista.nodes.size ≤ (store 46).length := by
    rw [source]
    exact Encoding.array_size_le_length _ _ (by intro node _;exact Encoding.node_positive_length node)
  have codeWidth : (index.val+1).size ≤ index.val+1:=Nat.size_le.mpr Nat.lt_two_pow_self
  have inside:=index.isLt
  let K:=(store 46).length+(store 32).length+steps.length+anchor.size+last.size+1
  have width : (index.val+1).size ≤ K := by dsimp only [K];omega
  have linear : K ≤ K^6:=Nat.le_self_pow (by decide) _
  have one : 1 ≤ K^6:=Nat.one_le_pow _ _ (by dsimp only [K];omega)
  change checkTime ≤ 81000000000000*K^6 at checkBound
  refine ⟨_,?_,a.sequence b⟩
  change checkTime+1+advanceTime ≤ 82000000000000*K^6
  omega

end Counting.StackMachine.AuditDescendant
