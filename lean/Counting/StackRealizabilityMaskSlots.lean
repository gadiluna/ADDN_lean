import Counting.StackRealizabilityMaskPrefix

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

def appendSlotBit (source scratch : Fin (registers+2)) (bit : Bool) : Routine registers:=
  sequence (ofProgram (ListPrograms.reverseProgram registers source scratch))
    (sequence (pushBit source bit) (ofProgram (ListPrograms.reverseProgram registers scratch source)))

theorem appendSlotBit_executes (source scratch : Fin (registers+2)) (different : source≠scratch)
    (store : Store registers) (bit : Bool) (empty : store scratch=[]) :
    Executes (appendSlotBit source scratch bit) store (4*(store source).length+5)
      (Function.update store source (store source++[bit])):=by
  have first:=reverse_executes registers source scratch different store
  rw [empty,List.append_nil] at first
  let reversed:=Function.update (Function.update store source []) scratch (store source).reverse
  have pushing:=pushBit_executes source bit reversed
  have sourceAt : reversed source=[]:=by simp [reversed,different]
  rw [sourceAt] at pushing
  let pushed:=Function.update reversed source [bit]
  have second:=reverse_executes registers scratch source different.symm pushed
  have scratchAt : pushed scratch=(store source).reverse:=by simp [pushed,reversed,different.symm]
  have targetAt : pushed source=[bit]:=by simp [pushed]
  rw [scratchAt,targetAt,List.length_reverse,List.reverse_reverse] at second
  have final : Function.update (Function.update pushed scratch []) source (store source++[bit])=
      Function.update store source (store source++[bit]):=by
    funext r
    by_cases rs : r=source
    · subst r;simp
    · by_cases rt : r=scratch
      · subst r;simp [different.symm,empty]
      · simp [pushed,reversed,rs,rt]
  rw [final] at second
  convert first.sequence (pushing.sequence second) using 1 <;> first | rfl | omega

/-- Append the inactive extra slot to the three node masks and increment the
explicit width. The hidden-population flag is calculated separately. -/
def maskSlots : Routine 28:=sequence maskPrefix
  (sequence (appendSlotBit 27 24 false)
    (sequence (appendSlotBit 28 24 false)
      (sequence (appendSlotBit 29 24 false) (pushBit 20 true))))

def maskSlotsStore (store : Store 28) (nodes : List Executable.Node) (suffix : List Bool)
    (old next : Nat) : Store 28:=
  Function.update (Function.update (Function.update (Function.update (Function.update store
    17 (Encoding.sequence Encoding.node nodes++suffix)) 20 (List.replicate (nodes.length+1) true))
    27 (nodes.map (fun node=>decide (node.level=old))++[false]))
    28 (nodes.map (fun node=>decide (node.level=next))++[false]))
    29 (nodes.map (fun node=>decide (0<node.degree))++[false])

theorem maskSlots_executes (store : Store 28) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀ r : Fin 30,r.val<17 → r≠1 → store r=[])
    (e18 : store 18=[]) (e19 : store 19=[]) (e20 : store 20=[]) (e21 : store 21=[])
    (e24 : store 24=[]) (e25 : store 25=[]) (e26 : store 26=[])
    (e27 : store 27=[]) (e28 : store 28=[]) (e29 : store 29=[])
    (nodes : List Executable.Node) (suffix : List Bool)
    (input : store 17=(Encoding.list Encoding.node).encode nodes++suffix)
    (old next : Nat) (oldAt : store 22=old.bits) (nextAt : store 23=next.bits) :
    ∃ time ≤ 12000*((store 17).length+old.size+next.size+1)^5,
      Executes maskSlots store time (maskSlotsStore store nodes suffix old next):=by
  obtain ⟨prefixTime,prefixBound,prefixRun⟩:=maskPrefix_executes store accepted tail status work
    e18 e19 e20 e21 e24 e25 e26 e27 e28 e29 nodes suffix input old next oldAt nextAt
  let prepared:=maskPrefixStore store nodes suffix old next
  have first:=appendSlotBit_executes (27:Fin 30) 24 (by decide) prepared false
    (by simp [prepared,maskPrefixStore,maskTableStore,e24])
  have firstAt : prepared 27=nodes.map (fun node=>decide (node.level=old)):=by
    simp [prepared,maskPrefixStore,maskTableStore]
  rw [firstAt,List.length_map] at first
  let oldDone:=Function.update prepared 27 (nodes.map (fun node=>decide (node.level=old))++[false])
  have second:=appendSlotBit_executes (28:Fin 30) 24 (by decide) oldDone false
    (by simp [oldDone,prepared,maskPrefixStore,maskTableStore,e24])
  have secondAt : oldDone 28=nodes.map (fun node=>decide (node.level=next)):=by
    simp [oldDone,prepared,maskPrefixStore,maskTableStore]
  rw [secondAt,List.length_map] at second
  let newDone:=Function.update oldDone 28 (nodes.map (fun node=>decide (node.level=next))++[false])
  have third:=appendSlotBit_executes (29:Fin 30) 24 (by decide) newDone false
    (by simp [newDone,oldDone,prepared,maskPrefixStore,maskTableStore,e24])
  have thirdAt : newDone 29=nodes.map (fun node=>decide (0<node.degree)):=by
    simp [newDone,oldDone,prepared,maskPrefixStore,maskTableStore]
  rw [thirdAt,List.length_map] at third
  let degreeDone:=Function.update newDone 29 (nodes.map (fun node=>decide (0<node.degree))++[false])
  have increment:=pushBit_executes (20:Fin 30) true degreeDone
  have widthAt : degreeDone 20=List.replicate nodes.length true:=by
    simp [degreeDone,newDone,oldDone,prepared,maskPrefixStore,maskTableStore]
  rw [widthAt] at increment
  have final : Function.update degreeDone 20 (true::List.replicate nodes.length true)=
      maskSlotsStore store nodes suffix old next:=by
    funext r
    fin_cases r <;> simp [degreeDone,newDone,oldDone,prepared,maskPrefixStore,maskTableStore,
      maskSlotsStore,List.replicate_succ]
  rw [final] at increment
  have count:=DagValidation.node_sequence_count_le nodes
  have width : nodes.length ≤ (store 17).length:=by
    rw [input]
    change nodes.length ≤ ((Encoding.natural.encode nodes.length++Encoding.sequence Encoding.node nodes)++suffix).length
    simp only [List.length_append]
    omega
  let S:=(store 17).length+old.size+next.size+1
  have linear : S ≤ S^5:=Nat.le_self_pow (by decide) _
  have one : 1 ≤ S^5:=Nat.one_le_pow _ _ (by dsimp only [S];omega)
  exact ⟨_,by change _ ≤ 12000*S^5;dsimp only [S] at linear one ⊢;omega,
    prefixRun.sequence (first.sequence (second.sequence (third.sequence increment)))⟩

end Counting.StackMachine.RealizabilityCheck
