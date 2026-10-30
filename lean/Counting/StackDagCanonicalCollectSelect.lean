import Counting.StackDagCanonicalCollectEmit
import Counting.StackEncodingBranch

namespace Counting.StackMachine.DagUpdate.Canonical
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

def chooseRecord : Routine 94 := branchRoutine 67 emitSelected (clear 3)

def chosenRecordStore (store : Store 94) (index : Nat) (node : Executable.Node) (selected : Bool) : Store 94 :=
  if selected then selectedRecordStore (Function.update store 67 []) index node
  else Function.update (Function.update store 67 []) 3 []

theorem chooseRecord_executes (store : Store 94) (index : Nat) (node : Executable.Node) (selected : Bool)
    (source : store 3=Encoding.node.encode node) (indexAt : store 83=List.replicate index true)
    (flag : store 67=[selected]) (e2 : store 2=[]) (e4 : store 4=[]) (e5 : store 5=[]) :
    ∃ time ≤ 101*(index+(Encoding.node.encode node).length+1)^2,
      Executes chooseRecord store time (chosenRecordStore store index node selected) := by
  let ready := Function.update store 67 []
  cases selected with
  | false =>
    have clear := clear_executes (3:Fin 96) ready
    rw [show ready 3=Encoding.node.encode node by simp [ready,source]] at clear
    have run := branch_executes_false (67:Fin 96) emitSelected (Routine.clear 3) store
      (Function.update ready 3 []) [] ((Encoding.node.encode node).length+1) flag clear
    refine ⟨_,?_,run⟩
    have linear : index+(Encoding.node.encode node).length+1≤
        (index+(Encoding.node.encode node).length+1)^2 := Nat.le_self_pow (by decide) _
    omega
  | true =>
    obtain ⟨time,bound,emit⟩ := emitSelected_executes ready index node
      (by simp [ready,source]) (by simp [ready,indexAt]) (by simp [ready,e2])
      (by simp [ready,e4]) (by simp [ready,e5])
    have run := branch_executes_true (67:Fin 96) emitSelected (clear 3) store
      (selectedRecordStore ready index node) [] time flag emit
    refine ⟨_,?_,run⟩
    have positive : 1≤(index+(Encoding.node.encode node).length+1)^2 := Nat.one_le_pow' _ _
    omega

end Counting.StackMachine.DagUpdate.Canonical
