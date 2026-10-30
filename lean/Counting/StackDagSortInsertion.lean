import Counting.StackDagSortLoop
import Counting.StackDagSortFinish
import Counting.DagSortInsertionBounds

namespace Counting.StackMachine.DagUpdate.Sort
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

def insertCore : Routine 94 := sequence insertionLoop finishInsertion

def insertionBudget (query : Record) (records : List Record) (sourceLength : Nat) : Nat :=
  records.length*(15000*(sourceLength+(recordCodec.encode query).length+1)^3+2)+
    11*(recordCodec.encode query).length+2*sourceLength+22

def insertCoreResult (store : Store 94) (query : Record) (records : List Record) (suffix : List Bool) : Store 94 :=
  Function.update (Function.update (Function.update (Function.update store 90 []) 80 suffix) 84 [])
    91 (Encoding.sequence recordCodec (List.orderedInsert (fun a b=>recordLE a b=true) query records))

/-- Exact physical stable insertion into a stream of indexed nodes.
The explicit counter is checked against the number of records in this
interface; the surrounding list-header parser supplies it in the sorter. -/
theorem insertCore_executes (store : Store 94) (query : Record) (records : List Record) (suffix : List Bool)
    (source : store 80=Encoding.sequence recordCodec records++suffix)
    (queryAt : store 64=Encoding.node.encode query.2) (recordAt : store 82=recordCodec.encode query)
    (status : store 81=[true]) (flagAt : store 84=[false])
    (counter : store 90=List.replicate records.length true) (outputEmpty : store 83=[] ∧ store 91=[])
    (empty : ∀ r : Fin 96,r.val≤14 ∨ (40≤r.val ∧ r.val≤44) ∨ (49≤r.val ∧ r.val≤51) ∨
      r=65 ∨ r=66 ∨ r=67 ∨ r=86 ∨ r=88 ∨ r=89 → store r=[]) :
    ∃ time ≤ insertionBudget query records (store 80).length,
      Executes insertCore store time (insertCoreResult store query records suffix) := by
  obtain ⟨loopTime,loopBound,loopRun⟩ := insertionLoop_executes store query records suffix false (store 80).length
    source queryAt recordAt status flagAt counter le_rfl empty
  let scanned := scanRecords query false records
  let middle := insertionLoopResult store query records suffix false
  have finish := finishInsertion_executes middle scanned.2
    (by simp [middle,insertionLoopResult,scanned])
    (by simp [middle,insertionLoopResult,empty])
    (by simp [middle,insertionLoopResult,empty])
    (by simp [middle,insertionLoopResult,empty])
    (by simp [middle,insertionLoopResult,outputEmpty])
  have word : finishInsertionWord middle scanned.2=
      Encoding.sequence recordCodec (List.orderedInsert (fun a b=>recordLE a b=true) query records) := by
    rw [←completedRecords_orderedInsert]
    change finishInsertionWord middle scanned.2=
      Encoding.sequence recordCodec (scanned.1++(if scanned.2 then [] else [query]))
    have outputAt : middle 83=(Encoding.sequence recordCodec scanned.1).reverse := by
      simp [middle,insertionLoopResult,outputEmpty,scanned]
    have queryAt' : middle 82=recordCodec.encode query := by
      simp [middle,insertionLoopResult,recordAt]
    cases flag : scanned.2 <;>
      simp [finishInsertionWord,outputAt,queryAt',sequence_append,Encoding.sequence,List.reverse_append]
  have final : Function.update (Function.update (Function.update middle 83 []) 84 [])
      91 (finishInsertionWord middle scanned.2)=insertCoreResult store query records suffix := by
    rw [word]
    funext r
    by_cases r90 : r=90 <;> by_cases r80 : r=80 <;> by_cases r83 : r=83 <;>
      by_cases r84 : r=84 <;> by_cases r91 : r=91 <;>
      simp [middle,insertionLoopResult,insertCoreResult,r90,r80,r83,r84,r91,outputEmpty]
  rw [final] at finish
  refine ⟨loopTime+1+finishInsertionCost middle scanned.2,?_,loopRun.sequence finish⟩
  have finishBound := finishInsertionCost_le middle scanned.2
  have codeBound := scanRecords_encoded_length_le query false records
  have outputSize : (middle 83).length=(Encoding.sequence recordCodec scanned.1).length := by
    simp [middle,insertionLoopResult,outputEmpty,scanned]
  have querySize : middle 82=recordCodec.encode query := by simp [middle,insertionLoopResult,recordAt]
  rw [outputSize,querySize] at finishBound
  rw [recordAt] at loopBound
  have sourceBound : (Encoding.sequence recordCodec records).length≤(store 80).length := by
    rw [source,List.length_append]
    omega
  change (Encoding.sequence recordCodec scanned.1).length≤_ at codeBound
  unfold insertionBudget
  omega

end Counting.StackMachine.DagUpdate.Sort
