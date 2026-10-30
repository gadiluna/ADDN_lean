import Counting.StackDagSortPending

namespace Counting.StackMachine.DagUpdate.Sort
open Routine
set_option backward.isDefEq.respectTransparency false

def finishInsertion : Routine 94 := sequence finishPending
  (sequence (ofProgram (ListPrograms.reverseProgram 94 83 91)) (clear 84))

def finishInsertionWord (store : Store 94) (inserted : Bool) : List Bool :=
  (if inserted then store 83 else (store 82).reverse++store 83).reverse

def finishInsertionCost (store : Store 94) (inserted : Bool) : Nat :=
  pendingCost store inserted+2*(finishInsertionWord store inserted).length+5

theorem finishInsertion_executes (store : Store 94) (inserted : Bool)
    (flagAt : store 84=[inserted]) (flagEmpty : store 66=[])
    (empty86 : store 86=[]) (empty89 : store 89=[]) (outputEmpty : store 91=[]) :
    Executes finishInsertion store (finishInsertionCost store inserted)
      (Function.update (Function.update (Function.update store 83 []) 84 [])
        91 (finishInsertionWord store inserted)) := by
  have pending := finishPending_executes store inserted flagAt flagEmpty empty86 empty89
  let completed := pendingResult store inserted
  have reverseRun := reverse_executes 94 (83:Fin 96) 91 (by decide) completed
  have source : completed 83=(if inserted then store 83 else (store 82).reverse++store 83) := by
    simp [completed,pendingResult]
  have target : completed 91=[] := by simp [completed,pendingResult,outputEmpty]
  rw [source,target,List.append_nil] at reverseRun
  let emitted := Function.update (Function.update completed 83 []) 91 (finishInsertionWord store inserted)
  have erase := clear_executes (84:Fin 96) emitted
  have flag : emitted 84=[true] := by simp [emitted,completed,pendingResult]
  rw [flag,List.length_singleton] at erase
  have final : Function.update emitted 84 []=
      Function.update (Function.update (Function.update store 83 []) 84 []) 91 (finishInsertionWord store inserted) := by
    funext r
    by_cases r83 : r=83 <;> by_cases r84 : r=84 <;> by_cases r91 : r=91 <;>
      simp [emitted,completed,pendingResult,r83,r84,r91]
  rw [final] at erase
  convert pending.sequence (reverseRun.sequence erase) using 1 <;>
    first | rfl | (simp [finishInsertionCost,finishInsertionWord];omega)

theorem finishInsertionCost_le (store : Store 94) (inserted : Bool) :
    finishInsertionCost store inserted≤9*(store 82).length+2*(store 83).length+20 := by
  cases inserted <;> simp [finishInsertionCost,pendingCost,finishInsertionWord,List.length_reverse,List.length_append] <;> omega

end Counting.StackMachine.DagUpdate.Sort
