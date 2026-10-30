import Counting.StackAuditDescendantPrepare
import Counting.StackDagIncrement

namespace Counting.StackMachine.AuditDescendant
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def advanceIndex : Routine 38 := sequence (DagValidation.incrementRoutine 37 0 37 1) (pushBit 36 true)

theorem advanceIndex_executes (store : Store 38) (index : Nat)
    (e0 : store 0=[]) (e1 : store 1=[]) (current : store 37=(index+1).bits) :
    ∃ time ≤ 4*(index+1).size+9,
      Executes advanceIndex store time
        (Function.update (Function.update store 37 (index+1+1).bits) 36 (true::store 36)) := by
  obtain ⟨time,bound,a⟩:=DagValidation.increment_natural 37 (0:Fin 40) 37 1
    (by decide) (by decide) (by decide) store e0 e1 (index+1) current
  have b:=pushBit_executes (36:Fin 40) true (Function.update store 37 (index+1+1).bits)
  have atIndex : Function.update store 37 (index+1+1).bits 36=store 36 := by simp
  rw [atIndex] at b
  exact ⟨_,by omega,a.sequence b⟩

def countCurrent : Routine 38 := sequence selectCurrent
  (sequence (branchRoutine 35 (pushBit 39 true) (skip 38)) advanceIndex)

def countItemResult (store : Store 38) (index : Nat) (hit : Bool) : Store 38 :=
  Function.update (Function.update (Function.update store 39
    (List.replicate (if hit then 1 else 0) true++store 39)) 37 (index+1+1).bits) 36 (true::store 36)

/-- One scan iteration reads and checks an actual stored node, increments
the descendant count if selected, and advances both persistent indices. -/
theorem countCurrent_executes (store : Store 38) (vista : Executable.Vista)
    (index : Fin vista.nodes.size) (last ancestor : Nat) (bits : List Bool)
    (source : store 17=Encoding.sequence Encoding.node vista.nodes.toList)
    (indexAt : (store 36).length=index.val) (current : store 37=(index.val+1).bits)
    (lastAt : store 34=last.bits) (target : store 29=(ancestor+1).bits)
    (counter : store 38=bits) (flag : store 35=[])
    (empty : ∀ r : Fin 40,r.val ≤ 28 → r≠17 → store r=[]) :
    ∃ time ≤ 15000000000*((store 17).length+bits.length+(ancestor+1).size+last.size+1)^5,
      Executes countCurrent store time
        (countItemResult store index.val (Executable.descendantSelected vista bits.length last ancestor index.val)) := by
  obtain ⟨selectTime,selectBound,a⟩:=selectCurrent_executes store vista index last ancestor bits
    source indexAt current lastAt target counter flag empty
  let hit:=Executable.descendantSelected vista bits.length last ancestor index.val
  let checked:=Function.update store 35 [hit]
  have popped : Function.update checked 35 []=store := by
    simp only [checked,Function.update_idem]
    rw [←flag,Function.update_eq_self]
  let K:=(store 17).length+bits.length+(ancestor+1).size+last.size+1
  have one : 1 ≤ K^5:=Nat.one_le_pow _ _ (by dsimp only [K];omega)
  have linear : K ≤ K^5:=Nat.le_self_pow (by decide) _
  have nodes:=DagValidation.node_sequence_count_le vista.nodes.toList
  rw [Array.length_toList,←source] at nodes
  have width : (index.val+1).size ≤ K := by
    have size : (index.val+1).size ≤ index.val+1 := Nat.size_le.mpr Nat.lt_two_pow_self
    have:=index.isLt
    dsimp only [K];omega
  change selectTime ≤ 14000000000*K^5 at selectBound
  cases answer:hit with
  | false=>
    have actual : Executable.descendantSelected vista bits.length last ancestor index.val=false := answer
    have branch:=branch_executes_false (35:Fin 40) (pushBit 39 true) (skip 38) checked store [] 0
      (by simp [checked,answer]) (by rw [popped];exact skip_executes store)
    obtain ⟨advanceTime,advanceBound,b⟩:=advanceIndex_executes store index.val
      (empty 0 (by decide) (by decide)) (empty 1 (by decide) (by decide)) current
    refine ⟨selectTime+1+(1+0+1+advanceTime),?_,?_⟩
    · change selectTime+1+(1+0+1+advanceTime) ≤ 15000000000*K^5
      omega
    · simpa only [countCurrent,countItemResult,actual,Bool.false_eq_true,if_false,List.replicate_zero,List.nil_append,Function.update_eq_self] using
        a.sequence (branch.sequence b)
  | true=>
    have actual : Executable.descendantSelected vista bits.length last ancestor index.val=true := answer
    have push:=pushBit_executes (39:Fin 40) true store
    let counted:=Function.update store 39 (true::store 39)
    have branch:=branch_executes_true (35:Fin 40) (pushBit 39 true) (skip 38) checked counted [] 1
      (by simp [checked,answer]) (by rw [popped];exact push)
    obtain ⟨advanceTime,advanceBound,b⟩:=advanceIndex_executes counted index.val
      (by simp [counted,empty]) (by simp [counted,empty]) (by simp [counted,current])
    refine ⟨selectTime+1+(1+1+1+advanceTime),?_,?_⟩
    · change selectTime+1+(1+1+1+advanceTime) ≤ 15000000000*K^5
      omega
    · simpa [countCurrent,countItemResult,actual,counted] using a.sequence (branch.sequence b)

end Counting.StackMachine.AuditDescendant
