import Counting.StackAuditAscendRead

namespace Counting.StackMachine.AuditAscend
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

theorem readParent_executes (store : Store 18) (nodes : List Executable.Node)
    (source : store 17=Encoding.sequence Encoding.node nodes)
    (status : store 1=[true])
    (empty : ∀ r : Fin 20,r≠1 → r≠17 → r≠18 → store r=[]) :
    ∃ time ≤ 10000*((store 17).length+(store 18).length+1)^4,
      Executes readParent store time
        (Function.update (Function.update store 1 []) 2
          (DagValidation.parentCode (nodes[(store 18).length]?.getD default)).bits) := by
  let index:=(store 18).length
  have work (r : Fin 17) (different : r≠1) : store (DagParser.nodeRoles r)=[] := by
    apply empty (DagParser.nodeRoles r)
    · exact fun eq=>different (DagParser.nodeRoles.injective eq)
    · intro eq;have := congrArg (fun r : Fin 20=>r.val) eq;dsimp [DagParser.nodeRoles] at this;omega
    · intro eq;have := congrArg (fun r : Fin 20=>r.val) eq;dsimp [DagParser.nodeRoles] at this;omega
  let K:=(store 17).length+index+1
  have positive : 1≤K := by dsimp only [K];omega
  have linear : K≤K^4 := Nat.le_self_pow (by decide) _
  have sourceBound : (store 17).length+1≤K := by dsimp only [K];omega
  have indexBound : 2*index+3≤3*K := by dsimp only [K];omega
  have readerBound : (2*index+3)*2029*((store 17).length+1)^3 ≤ 6087*K^4 := by
    calc
      _ ≤ (3*K)*2029*K^3 := by gcongr
      _ = _ := by ring
  by_cases inside : index<nodes.length
  · let selected : Fin nodes.length:=⟨index,inside⟩
    obtain ⟨time,bound,a⟩:=DagParser.preservingNodeRead_get store true [] status work
      (empty 19 (by decide) (by decide) (by decide)) nodes selected [] (by simpa using source) rfl
    let read:=Function.update store 19 (Encoding.node.encode nodes[selected])
    let popped:=Function.update read 1 []
    obtain ⟨metadataTime,metadataBound,b⟩:=readMetadata_executes popped nodes[selected]
      (by simp [popped,read]) (by
        intro r member
        simp only [List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl|rfl|rfl|rfl|rfl <;> simp [popped,read,empty])
    have branch:=branch_executes_true (1:Fin 20) readMetadata (clear 19) read
      (Function.update (Function.update popped 19 []) 2 (DagValidation.parentCode nodes[selected]).bits)
      [] metadataTime (by simp [read,status]) b
    have final : Function.update (Function.update popped 19 []) 2 (DagValidation.parentCode nodes[selected]).bits=
        Function.update (Function.update store 1 []) 2
          (DagValidation.parentCode (nodes[(store 18).length]?.getD default)).bits := by
      funext r
      by_cases a:r=1 <;> by_cases b:r=2 <;> by_cases c:r=19 <;>
        simp [popped,read,a,b,c,empty,selected,index,List.getElem?_eq_getElem inside]
    rw [final] at branch
    have nodeBound:=DagValidation.node_sequence_member_le nodes nodes[selected] (List.getElem_mem selected.isLt)
    rw [←source] at nodeBound
    refine ⟨_,?_,a.sequence branch⟩
    change _ ≤ 10000*K^4
    change time ≤ (2*index+3)*2029*((store 17).length+1)^3+6*(store 17).length+7*index+14 at bound
    dsimp only [K,index] at linear readerBound bound ⊢
    omega
  · obtain ⟨time,bound,a⟩:=DagParser.preservingNodeRead_executes store true [] status work
      (empty 19 (by decide) (by decide) (by decide))
    let effect:=DagParser.nodeReadEffect index (store 17)
    have rejected : effect.accepted=false := by
      rw [show effect=DagParser.nodeReadEffect index (Encoding.sequence Encoding.node nodes) by simp [effect,source]]
      exact nodeRead_outside nodes index (by omega)
    let read:=DagParser.preservingNodeStore store true [] effect
    let popped:=Function.update read 1 []
    have b:=clear_executes (19:Fin 20) popped
    have output : popped 19=effect.code := by simp [popped,read,DagParser.preservingNodeStore]
    rw [output] at b
    have branch:=branch_executes_false (1:Fin 20) readMetadata (clear 19) read
      (Function.update popped 19 []) [] (effect.code.length+1)
      (by simp [read,DagParser.preservingNodeStore,rejected]) b
    have final : Function.update popped 19 []=Function.update (Function.update store 1 []) 2
        (DagValidation.parentCode (nodes[(store 18).length]?.getD default)).bits := by
      have missing : nodes[(store 18).length]?=none := List.getElem?_eq_none (by omega)
      simp only [missing,Option.getD_none]
      change Function.update popped 19 []=Function.update (Function.update store 1 []) 2 []
      funext r
      by_cases a:r=1 <;> by_cases b:r=2 <;> by_cases c:r=19 <;>
        simp [popped,read,DagParser.preservingNodeStore,a,b,c,empty]
    rw [final] at branch
    have codeBound:=DagParser.node.read_code_le index (store 17)
    change effect.code.length ≤ 2029*((store 17).length+1)^3 at codeBound
    have cube : ((store 17).length+1)^3 ≤ K^4 := by
      calc
        _ ≤ K^3 := Nat.pow_le_pow_left sourceBound 3
        _ ≤ K^4 := Nat.pow_le_pow_right positive (by decide)
    refine ⟨_,?_,a.sequence branch⟩
    change _ ≤ 10000*K^4
    change time ≤ (2*index+3)*2029*((store 17).length+1)^3+6*(store 17).length+7*index+14 at bound
    dsimp only [K,index] at linear readerBound bound cube ⊢
    omega

end Counting.StackMachine.AuditAscend

