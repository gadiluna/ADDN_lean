import Counting.StackRealizabilityMaskLoop

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

theorem maskRange_map (nodes : List Executable.Node) (predicate : Executable.Node → Bool)
    (start count : Nat) : maskRange nodes predicate start count=
      (List.range count).map (fun i=>predicate (nodes[start+i]?.getD default)):=by
  induction count generalizing start with
  | zero=>rfl
  | succ count ih=>
    simp only [maskRange,ih,List.range_succ_eq_map,List.map_cons,List.map_map,Nat.add_zero]
    congr 1
    apply congrArg (fun f=>(List.range count).map f)
    funext i
    rw [show start+1+i=start+(i+1) by omega]
    rfl

theorem maskRange_all (nodes : List Executable.Node) (predicate : Executable.Node → Bool) :
    maskRange nodes predicate 0 nodes.length=nodes.map predicate:=by
  rw [maskRange_map]
  apply List.ext_getElem
  · simp
  · intro i left right
    have inside : i<nodes.length:=by simpa using left
    simp only [List.getElem_map,List.getElem_range,Nat.zero_add,List.getElem?_eq_getElem inside,Option.getD_some]

/-- Three masks are emitted in node order in registers 27, 28, 29. The
explicit width in register 20 bounds the loop; source and both levels remain. -/
def maskTable : Routine 28:=sequence (ofProgram (ListPrograms.copyProgram 27 20 21 4))
  (sequence (forEach 21 maskItem) (sequence (clear 18)
    (sequence (ofProgram (ListPrograms.reverseProgram 28 24 27))
      (sequence (ofProgram (ListPrograms.reverseProgram 28 25 28))
        (ofProgram (ListPrograms.reverseProgram 28 26 29))))))

def maskTableStore (store : Store 28) (nodes : List Executable.Node) (old next : Nat) : Store 28:=
  Function.update (Function.update (Function.update store
    27 (nodes.map (fun node=>decide (node.level=old))))
    28 (nodes.map (fun node=>decide (node.level=next))))
    29 (nodes.map (fun node=>decide (0<node.degree)))

theorem maskTable_executes (store : Store 28) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀ r : Fin 30,r.val<17 → r≠1 → store r=[])
    (e18 : store 18=[]) (e19 : store 19=[]) (e21 : store 21=[])
    (e24 : store 24=[]) (e25 : store 25=[]) (e26 : store 26=[])
    (e27 : store 27=[]) (e28 : store 28=[]) (e29 : store 29=[])
    (nodes : List Executable.Node) (suffix : List Bool)
    (input : store 17=Encoding.sequence Encoding.node nodes++suffix)
    (count : (store 20).length=nodes.length)
    (old next : Nat) (oldAt : store 22=old.bits) (nextAt : store 23=next.bits) :
    ∃ time ≤ 9000*((store 17).length+old.size+next.size+1)^5,
      Executes maskTable store time (maskTableStore store nodes old next):=by
  have copying:=copy_executes 27 20 21 4 (by decide) (by decide) (by decide) store (work 4 (by decide) (by decide))
  rw [e21,List.append_nil] at copying
  let prepared:=Function.update store 21 (store 20)
  have preparedWork (r : Fin 30) (small : r.val<17) (different : r≠1) : prepared r=[]:=by
    have ne : r≠21:=by intro same;subst r;norm_num at small
    simp [prepared,ne,work r small different]
  obtain ⟨loopTime,loopBound,loopRun⟩:=maskLoop_executes prepared accepted tail
    (by simp [prepared,status]) preparedWork (by simp [prepared,e19]) (by simp [prepared,e27])
    nodes 0 (store 20) (by omega) suffix (by simp [prepared,input])
    (by simp [prepared,e18]) (by simp [prepared]) old next (by simp [prepared,oldAt]) (by simp [prepared,nextAt])
  rw [count] at loopRun loopBound
  let scanned:=maskLoopStore prepared nodes old next 0 nodes.length
  have cleaning:=clear_executes (18:Fin 30) scanned
  have indexAt : scanned 18=List.replicate nodes.length true:=by simp [scanned,maskLoopStore,prepared,e18]
  rw [indexAt,List.length_replicate] at cleaning
  let cleaned:=Function.update scanned 18 []
  have first:=reverse_executes 28 24 27 (by decide) cleaned
  have oldMask : cleaned 24=(nodes.map (fun node=>decide (node.level=old))).reverse:=by
    simp [cleaned,scanned,maskLoopStore,prepared,e24,maskRange_all]
  have firstEmpty : cleaned 27=[]:=by simp [cleaned,scanned,maskLoopStore,prepared,e27]
  rw [oldMask,firstEmpty,List.append_nil,List.reverse_reverse,List.length_reverse,List.length_map] at first
  let oldDone:=Function.update (Function.update cleaned 24 []) 27 (nodes.map (fun node=>decide (node.level=old)))
  have second:=reverse_executes 28 25 28 (by decide) oldDone
  have newMask : oldDone 25=(nodes.map (fun node=>decide (node.level=next))).reverse:=by
    simp [oldDone,cleaned,scanned,maskLoopStore,prepared,e25,maskRange_all]
  have secondEmpty : oldDone 28=[]:=by simp [oldDone,cleaned,scanned,maskLoopStore,prepared,e28]
  rw [newMask,secondEmpty,List.append_nil,List.reverse_reverse,List.length_reverse,List.length_map] at second
  let newDone:=Function.update (Function.update oldDone 25 []) 28 (nodes.map (fun node=>decide (node.level=next)))
  have third:=reverse_executes 28 26 29 (by decide) newDone
  have degreeMask : newDone 26=(nodes.map (fun node=>decide (0<node.degree))).reverse:=by
    simp [newDone,oldDone,cleaned,scanned,maskLoopStore,prepared,e26,maskRange_all]
  have thirdEmpty : newDone 29=[]:=by simp [newDone,oldDone,cleaned,scanned,maskLoopStore,prepared,e29]
  rw [degreeMask,thirdEmpty,List.append_nil,List.reverse_reverse,List.length_reverse,List.length_map] at third
  have final : Function.update (Function.update newDone 26 []) 29 (nodes.map (fun node=>decide (0<node.degree)))=
      maskTableStore store nodes old next:=by
    funext r
    fin_cases r <;> simp [newDone,oldDone,cleaned,scanned,maskLoopStore,prepared,maskTableStore,
      e18,e21,e24,e25,e26]
  rw [final] at third
  have nodeCount:=DagValidation.node_sequence_count_le nodes
  have lengthBound : nodes.length ≤ (store 17).length:=by rw [input,List.length_append];omega
  let S:=(store 17).length+old.size+next.size+1
  have width : nodes.length ≤ S:=by dsimp only [S];omega
  have loopLimit : loopTime ≤ 8000*S^5+2*S+1:=by
    have same : prepared 17=store 17:=by simp [prepared]
    rw [same] at loopBound
    have b : loopTime ≤ S*(8000*S^4+2)+1:=by
      apply loopBound.trans
      exact Nat.add_le_add_right (Nat.mul_le_mul_right _ width) 1
    have expansion (x : Nat) : x*(8000*x^4+2)+1=8000*x^5+2*x+1:=by ring
    exact expansion S ▸ b
  have linear : S ≤ S^5:=Nat.le_self_pow (by decide) _
  have one : 1 ≤ S^5:=Nat.one_le_pow _ _ (by dsimp only [S];omega)
  rw [count] at copying
  exact ⟨_,by change _ ≤ 9000*S^5;dsimp only [S] at loopLimit linear one ⊢;omega,
    copying.sequence (loopRun.sequence (cleaning.sequence (first.sequence (second.sequence third))))⟩

end Counting.StackMachine.RealizabilityCheck
