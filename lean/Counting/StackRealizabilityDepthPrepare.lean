import Counting.StackRealizabilityInputCount
import Counting.StackFrameSkip
import Counting.StackRoutineFixedPrefix

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false

def depthPrepare : Routine 98 := sequence (ofProgram (ListPrograms.copyProgram 97 80 70 0))
  (sequence (ofProgram (FieldAccess.skipProgram 98 70))
    (sequence (ofProgram (ListPrograms.copyProgram 97 87 73 0)) (discardBit 73)))

def depthPreparedStore (vista : Executable.Vista) (values : List Nat) (ell order : Nat)
    (status : List Bool) : Store 98 :=
  Function.update (Function.update (inputCountStore vista values ell order status)
    70 (Encoding.sequence Encoding.node vista.nodes.toList))
    73 (List.replicate (vista.nodes.size-1) true)

/-- The last-node index is obtained by copying the explicit table count
and popping one bit. No binary index is expanded without an input budget. -/
theorem depthPrepare_executes (vista : Executable.Vista) (values : List Nat) (ell order : Nat)
    (status : List Bool) :
    ∃ time ≤ 20*(((Encoding.list Encoding.node).encode vista.nodes.toList).length+vista.nodes.size+1),
      Executes depthPrepare (inputCountStore vista values ell order status) time
        (depthPreparedStore vista values ell order status) := by
  let start := inputCountStore vista values ell order status
  let word := (Encoding.list Encoding.node).encode vista.nodes.toList
  have first := copy_executes 97 (80:Fin 100) 70 0 (by decide) (by decide) (by decide)
    start (by simp [start,inputCountStore,inputNodesStore,inputFieldsStore])
  have sourceAt : start 80=word := by simp [start,inputCountStore,inputNodesStore,word]
  have emptyAt : start 70=[] := by simp [start,inputCountStore,inputNodesStore,inputFieldsStore]
  rw [sourceAt,emptyAt,List.append_nil] at first
  let copied := Function.update start 70 word
  have skipping := FieldAccess.skip_executes 98 (70:Fin 100) copied
  have copiedAt : copied 70=word := by simp [copied]
  rw [copiedAt] at skipping
  have suffix : FieldAccess.skipRest word=Encoding.sequence Encoding.node vista.nodes.toList := by
    exact FieldAccess.skipRest_frame vista.nodes.toList.length.bits _
  rw [suffix,Function.update_idem] at skipping
  let sequenceStore := Function.update start 70 (Encoding.sequence Encoding.node vista.nodes.toList)
  have indexCopy := copy_executes 97 (87:Fin 100) 73 0 (by decide) (by decide) (by decide)
    sequenceStore (by simp [sequenceStore,start,inputCountStore,inputNodesStore,inputFieldsStore])
  have indexAt : sequenceStore 87=List.replicate vista.nodes.size true := by
    simp [sequenceStore,start,inputCountStore]
  have targetAt : sequenceStore 73=[] := by
    simp [sequenceStore,start,inputCountStore,inputNodesStore,inputFieldsStore]
  rw [indexAt,targetAt,List.append_nil,List.length_replicate] at indexCopy
  let indexed := Function.update sequenceStore 73 (List.replicate vista.nodes.size true)
  have popping := discardBit_executes (73:Fin 100) indexed
  have tailAt : indexed 73=List.replicate vista.nodes.size true := by simp [indexed]
  rw [tailAt,List.tail_replicate,Function.update_idem] at popping
  have skipBound := FieldAccess.skipCost_le word
  exact ⟨_,by change 5*word.length+2+1+(FieldAccess.skipCost word+1+(5*vista.nodes.size+2+1+1)) ≤
      20*(word.length+vista.nodes.size+1);omega,
    first.sequence (skipping.sequence (indexCopy.sequence popping))⟩

end Counting.StackMachine.RealizabilityCheck
