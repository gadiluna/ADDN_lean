import Counting.StackDagSortRecord
import Counting.StackEmitNatural
import Counting.StackRoutineMove

namespace Counting.StackMachine.DagUpdate.Canonical
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

def collectIndexRoles : PowerWorkspace 91 := ⟨![83,3,2,4,5],by decide⟩

def emitSelected : Routine 94 := sequence (emitNatural 91 collectIndexRoles)
  (sequence (move 93 3 85 4) (pushBit 86 true))

def selectedRecordStore (store : Store 94) (index : Nat) (node : Executable.Node) : Store 94 :=
  Function.update (Function.update (Function.update store 3 [])
    85 (Sort.recordCodec.encode (index,node)++store 85)) 86 (true::store 86)

theorem emitSelected_executes (store : Store 94) (index : Nat) (node : Executable.Node)
    (source : store 3=Encoding.node.encode node) (indexAt : store 83=List.replicate index true)
    (e2 : store 2=[]) (e4 : store 4=[]) (e5 : store 5=[]) :
    ∃ time ≤ 100*(index+(Encoding.node.encode node).length+1)^2,
      Executes emitSelected store time (selectedRecordStore store index node) := by
  obtain ⟨time,bound,emit⟩ := emitNatural_executes 91 collectIndexRoles store e2 e4 e5
  change time≤20*((store 83).length+1)^2 at bound
  change Executes (emitNatural 91 collectIndexRoles) store time
    (Function.update store 3 (Encoding.natural.encode (store 83).length++store 3)) at emit
  rw [indexAt,List.length_replicate,source] at emit
  rw [indexAt,List.length_replicate] at bound
  let a := Function.update store 3 (Sort.recordCodec.encode (index,node))
  have move := move_executes 93 (3:Fin 96) 85 4 (by decide) (by decide) (by decide) a (by simp [a,e4])
  rw [show a 3=Sort.recordCodec.encode (index,node) by simp [a],show a 85=store 85 by simp [a]] at move
  let b := Function.update (Function.update a 85 (Sort.recordCodec.encode (index,node)++store 85)) 3 []
  have push := pushBit_executes (86:Fin 96) true b
  have final : Function.update b 86 (true::b 86)=selectedRecordStore store index node := by
    funext r
    by_cases r3:r=3 <;> by_cases r85:r=85 <;> by_cases r86:r=86 <;>
      simp [selectedRecordStore,b,a,r3,r85,r86]
  rw [final] at push
  refine ⟨_,?_,emit.sequence (move.sequence push)⟩
  have size : index.size ≤ index := Nat.size_le.mpr Nat.lt_two_pow_self
  have length : (Sort.recordCodec.encode (index,node)).length=2*index.size+1+(Encoding.node.encode node).length := by
    simp only [Sort.recordCodec,Encoding.product,List.length_append,Encoding.natural_length]
  rw [length]
  nlinarith

end Counting.StackMachine.DagUpdate.Canonical
