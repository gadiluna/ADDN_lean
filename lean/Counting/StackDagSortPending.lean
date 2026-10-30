import Counting.StackDagSortSelect

namespace Counting.StackMachine.DagUpdate.Sort
open Routine
set_option backward.isDefEq.respectTransparency false

def finishPending : Routine 94 := sequence (pushBit 66 true) selectInsertion

def pendingCost (store : Store 94) (inserted : Bool) : Nat :=
  if inserted then 7 else 7*(store 82).length+15

def pendingResult (store : Store 94) (inserted : Bool) : Store 94 :=
  Function.update (Function.update store 84 [true])
    83 (if inserted then store 83 else (store 82).reverse++store 83)

/-- At the end of the scan, emit a query that was not inserted earlier.
This uses the same concrete insertion controller with a stored true bit. -/
theorem finishPending_executes (store : Store 94) (inserted : Bool)
    (flagAt : store 84=[inserted]) (flagEmpty : store 66=[])
    (empty86 : store 86=[]) (empty89 : store 89=[]) :
    Executes finishPending store (pendingCost store inserted) (pendingResult store inserted) := by
  have push := pushBit_executes (66:Fin 96) true store
  rw [flagEmpty] at push
  let marked := Function.update store 66 [true]
  have select := selectInsertion_executes marked inserted true (by simp [marked,flagAt])
    (by simp [marked]) (by simp [marked,empty86]) (by simp [marked,empty89])
  have final : selectedStore marked inserted true=pendingResult store inserted := by
    funext r
    by_cases r66 : r=66 <;> by_cases r83 : r=83 <;> by_cases r84 : r=84 <;> cases inserted <;>
      simp [marked,selectedStore,pendingResult,r66,r83,r84,flagEmpty]
  rw [final] at select
  convert push.sequence select using 1 <;> first | rfl | (cases inserted <;> simp [pendingCost,selectionCost,marked];omega)

end Counting.StackMachine.DagUpdate.Sort
