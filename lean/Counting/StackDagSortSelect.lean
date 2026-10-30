import Counting.StackRoutineCopyReverse
import Counting.StackReadBranch

namespace Counting.StackMachine.DagUpdate.Sort
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

def queryCopyRoles : Fin 4 ↪ Fin 96 := ⟨![82,83,86,89],by decide⟩

def emitQuery : Routine 94 := sequence (copyReverse 92 queryCopyRoles)
  (sequence (clear 84) (pushBit 84 true))

def selectInsertion : Routine 94 := branchRead 84 (clear 66)
  (branchRoutine 66 emitQuery (skip 94))

def selectedStore (store : Store 94) (inserted before : Bool) : Store 94 :=
  Function.update (Function.update (Function.update store 66 []) 84 [inserted || before])
    83 (if !inserted && before then (store 82).reverse++store 83 else store 83)

def selectionCost (store : Store 94) (inserted before : Bool) : Nat :=
  if inserted then 5 else if before then 7*(store 82).length+13 else 4

private theorem emitQuery_executes (store : Store 94)
    (openAt : store 84=[false]) (empty86 : store 86=[]) (empty89 : store 89=[]) :
    Executes emitQuery store (7*(store 82).length+9)
      (Function.update (Function.update store 83 ((store 82).reverse++store 83)) 84 [true]) := by
  have copy := copyReverse_executes 92 queryCopyRoles store empty86 empty89
  let copied := Function.update store 83 ((store 82).reverse++store 83)
  change Executes (copyReverse 92 queryCopyRoles) store (7*(store 82).length+4) copied at copy
  have erase := clear_executes (84:Fin 96) copied
  have oldFlag : copied 84=[false] := by simp [copied,openAt]
  rw [oldFlag,List.length_singleton] at erase
  let erased := Function.update copied 84 []
  have mark := pushBit_executes (84:Fin 96) true erased
  have nowEmpty : erased 84=[] := by simp [erased]
  rw [nowEmpty] at mark
  simpa only [emitQuery,copied,erased,Function.update_idem] using copy.sequence (erase.sequence mark)

/-- Emit the query exactly once, immediately before the first qualifying
record. The insertion flag and comparison flag are ordinary stored bits. -/
theorem selectInsertion_executes (store : Store 94) (inserted before : Bool)
    (insertedAt : store 84=[inserted]) (compareAt : store 66=[before])
    (empty86 : store 86=[]) (empty89 : store 89=[]) :
    Executes selectInsertion store (selectionCost store inserted before) (selectedStore store inserted before) := by
  cases inserted with
  | true =>
    have erase := clear_executes (66:Fin 96) store
    rw [compareAt,List.length_singleton] at erase
    have final : Function.update store 66 []=selectedStore store true before := by
      funext r
      by_cases r66 : r=66 <;> by_cases r83 : r=83 <;> by_cases r84 : r=84 <;>
        simp [selectedStore,r66,r83,r84,insertedAt]
    rw [final] at erase
    exact branchRead_executes (84:Fin 96) (clear 66) (branchRoutine 66 emitQuery (skip 94)) true []
      store _ 2 insertedAt erase
  | false =>
    cases before with
    | false =>
      let consumed := Function.update store 66 []
      have final : consumed=selectedStore store false false := by
        funext r
        by_cases r66 : r=66 <;> by_cases r83 : r=83 <;> by_cases r84 : r=84 <;>
          simp [consumed,selectedStore,r66,r83,r84,insertedAt]
      have skipRun : Executes (skip 94) consumed 0 (selectedStore store false false) := final ▸ skip_executes consumed
      have chosen := branch_executes_false (66:Fin 96) emitQuery (skip 94) store _ [] 0 compareAt skipRun
      exact branchRead_executes (84:Fin 96) (clear 66) (branchRoutine 66 emitQuery (skip 94)) false []
        store _ 1 insertedAt chosen
    | true =>
      let consumed := Function.update store 66 []
      have emit := emitQuery_executes consumed (by simp [consumed,insertedAt])
        (by simp [consumed,empty86]) (by simp [consumed,empty89])
      have source : consumed 82=store 82 := by simp [consumed]
      rw [source] at emit
      have final : Function.update (Function.update consumed 83 ((store 82).reverse++consumed 83)) 84 [true]=
          selectedStore store false true := by
        funext r
        by_cases r66 : r=66 <;> by_cases r83 : r=83 <;> by_cases r84 : r=84 <;>
          simp [consumed,selectedStore,r66,r83,r84]
      rw [final] at emit
      have chosen := branch_executes_true (66:Fin 96) emitQuery (skip 94) store _ [] _ compareAt emit
      have selected := branchRead_executes (84:Fin 96) (clear 66) (branchRoutine 66 emitQuery (skip 94)) false []
        store _ _ insertedAt chosen
      convert selected using 1 <;> first | rfl | (simp [selectionCost];omega)

end Counting.StackMachine.DagUpdate.Sort
