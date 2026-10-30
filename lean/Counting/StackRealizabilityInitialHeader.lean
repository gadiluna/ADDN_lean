import Counting.StackDagSelectedHeader
import Counting.StackDagParentBounds

namespace Counting.StackMachine.RealizabilityCheck
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

def initialHeaderRoles : Fin 20 ↪ Fin 26 where
  toFun r:=⟨r.val,by omega⟩
  inj':=by intro a b same;apply Fin.ext;exact congrArg (fun r:Fin 26=>r.val) same

def initialHeader : Routine 24:=mapRegisters initialHeaderRoles DagValidation.selectedHeader

def initialHeaderStore (store : Store 24) (node : Executable.Node) : Store 24:=
  fun r=>if r=19 then DagValidation.nodeSuffix node else if r=0 then node.level.bits
    else if r=2 then (DagValidation.parentCode node).bits else if r=3 then [node.leader] else store r

theorem initialHeader_executes (store : Store 24) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀ r : Fin 26,r.val<17 → r≠1 → store r=[])
    (e19 : store 19=[]) (nodes : List Executable.Node) (index : Fin nodes.length)
    (suffix : List Bool) (input : store 17=Encoding.sequence Encoding.node nodes++suffix)
    (counter : (store 18).length=index.val) :
    ∃ time ≤ 7000*((store 17).length+1)^4,
      Executes initialHeader store time (initialHeaderStore store nodes[index]):=by
  let original : Store 18:=store ∘ initialHeaderRoles
  have originalWork (r : Fin 17) (different : r≠1) : original (DagParser.nodeRoles r)=[]:=by
    apply work (initialHeaderRoles (DagParser.nodeRoles r)) (by exact r.isLt)
    intro same
    apply different
    apply Fin.ext
    simpa [initialHeaderRoles,DagParser.nodeRoles] using congrArg (fun r:Fin 26=>r.val) same
  obtain ⟨time,bound,ran⟩:=DagValidation.selectedHeader_get original accepted tail status originalWork e19
    nodes index suffix input counter
  have relocated : Executes initialHeader store time (initialHeaderStore store nodes[index]):=by
    apply relocate_executes_frame DagValidation.selectedHeader initialHeaderRoles store _ original
      (DagValidation.selectedHeaderStore original nodes[index]) time rfl _ _ ran
    · intro r
      fin_cases r <;> simp [initialHeaderStore,DagValidation.selectedHeaderStore,original,initialHeaderRoles]
    · intro r outside
      have n0 : r≠0:=by intro same;subst r;exact outside 0 rfl
      have n2 : r≠2:=by intro same;subst r;exact outside 2 rfl
      have n3 : r≠3:=by intro same;subst r;exact outside 3 rfl
      have n19 : r≠19:=by intro same;subst r;exact outside 19 rfl
      simp [initialHeaderStore,n0,n2,n3,n19]
  change time≤(2*(store 18).length+3)*2029*((store 17).length+1)^3+
    6*(store 17).length+7*(store 18).length+6*(Encoding.node.encode nodes[index]).length+36 at bound
  rw [counter] at bound
  have entryCount:=DagValidation.node_sequence_count_le nodes
  have entryLength:=DagValidation.node_sequence_member_le nodes nodes[index] (List.getElem_mem index.isLt)
  have indexBound : index.val≤(store 17).length:=by rw [input,List.length_append];have:=index.isLt;omega
  have nodeBound : (Encoding.node.encode nodes[index]).length≤(store 17).length:=by rw [input,List.length_append];omega
  let S:=(store 17).length+1
  have factor : 2*index.val+3≤3*S:=by dsimp only [S];omega
  have leading : (2*index.val+3)*2029*((store 17).length+1)^3≤6087*S^4:=by
    calc
      _ ≤ (3*S)*2029*S^3:=by gcongr
      _ = _:=by ring
  have linear : S≤S^4:=Nat.le_self_pow (by decide) _
  refine ⟨time,?_,relocated⟩
  change time≤7000*S^4
  dsimp only [S] at leading linear ⊢
  omega

end Counting.StackMachine.RealizabilityCheck
