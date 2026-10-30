import Counting.StackEncodingPairSemantics
import Counting.StackComparePreserving
import Counting.StackUnaryBranch
import Counting.StackRoutineLists
import Counting.StackRoutineMove

/-! A binary sparse-edge search step. Both identifiers and multiplicities
remain binary words. The first matching edge is retained even when its
multiplicity is zero or later entries repeat the same identifier. -/
namespace Counting.StackMachine.AnchorFind
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

/-- The final cell is a live loop counter and is preserved by every item. -/
def file (input query key value result pending equality counter : List Bool) : Store 11 :=
  ![input,query,key,value,result,pending,[],equality,[],[],[],[],counter]

def pairRoles : Fin 5 ↪ Fin 13 := ⟨![0,2,3,8,6],by decide⟩
def equalityRoles : Fin 6 ↪ Fin 13 := ⟨![1,2,7,8,9,10],by decide⟩
abbrev takeValue : Routine 11 := sequence (clear 4) (sequence (move 10 3 4 11) (pushBit 5 false))
abbrev compareValue : Routine 11 := sequence (Compare.preservingEquality 7 equalityRoles)
  (branchRoutine 7 takeValue (pushBit 5 true))
abbrev dispatch : Routine 11 := branchRoutine 5 compareValue (pushBit 5 false)
abbrev cleanup : Routine 11 := sequence (clear 2) (clear 3)
abbrev item : Routine 11 := sequence (pairRoutine 8 pairRoles) (sequence (clear 6) (sequence dispatch cleanup))

theorem takeValue_executes (input query key value result counter : List Bool) :
    Executes takeValue (file input query key value result [] [] counter)
      (result.length+6*value.length+8)
      (file input query key [] value [false] [] counter) := by
  have erased := clear_executes (4:Fin 13) (file input query key value result [] [] counter)
  have eraseStore : Function.update (file input query key value result [] [] counter) 4 []=
      file input query key value [] [] [] counter := by funext r;fin_cases r <;> simp [file]
  rw [eraseStore] at erased
  have moved := move_executes 10 (3:Fin 13) 4 11 (by decide) (by decide) (by decide)
    (file input query key value [] [] [] counter) rfl
  have moveStore : Function.update (Function.update (file input query key value [] [] [] counter) 4
      (value++[])) 3 []=file input query key [] value [] [] counter := by
    funext r;fin_cases r <;> simp [file]
  change Executes _ _ (6*value.length+4)
    (Function.update (Function.update (file input query key value [] [] [] counter) 4 (value++[])) 3 []) at moved
  rw [moveStore] at moved
  have marked := pushBit_executes (5:Fin 13) false (file input query key [] value [] [] counter)
  have markStore : Function.update (file input query key [] value [] [] counter) 5 [false]=
      file input query key [] value [false] [] counter := by funext r;fin_cases r <;> simp [file]
  change Executes _ _ 1 (Function.update (file input query key [] value [] [] counter) 5 [false]) at marked
  rw [markStore] at marked
  have combined := erased.sequence (moved.sequence marked)
  convert combined using 1
  simp [file]
  omega

theorem dispatch_executes (input query key value result counter : List Bool) (pending : Bool) :
    ∃ time ≤ 30*(query.length+key.length+value.length+result.length+1),
      Executes dispatch (file input query key value result [pending] [] counter) time
        (file input query key (if pending && decide (query=key) then [] else value)
          (if pending && decide (query=key) then value else result)
          [pending && !decide (query=key)] [] counter) := by
  cases pending with
  | false =>
    have pushed := pushBit_executes (5:Fin 13) false (file input query key value result [] [] counter)
    have same : Function.update (file input query key value result [] [] counter) 5 [false]=
        file input query key value result [false] [] counter := by funext r;fin_cases r <;> simp [file]
    change Executes _ _ 1 (Function.update (file input query key value result [] [] counter) 5 [false]) at pushed
    rw [same] at pushed
    have erased : Function.update (file input query key value result [false] [] counter) 5 []=
        file input query key value result [] [] counter := by funext r;fin_cases r <;> simp [file]
    have ran := branch_executes_false (5:Fin 13) compareValue (pushBit 5 false)
      (file input query key value result [false] [] counter)
      (file input query key value result [false] [] counter) [] 1 rfl (erased.symm ▸ pushed)
    exact ⟨2,by omega,by simpa [dispatch] using ran⟩
  | true =>
    have compared := Compare.preservingEquality_executes 7 equalityRoles
      (file input query key value result [] [] counter) rfl rfl rfl
    have comparedStore : Function.update (file input query key value result [] [] counter) 7 [decide (query=key)]=
        file input query key value result [] [decide (query=key)] counter := by
      funext r;fin_cases r <;> simp [file]
    change Executes _ _ (Compare.preservingCost query key)
      (Function.update (file input query key value result [] [] counter) 7 [decide (query=key)]) at compared
    rw [comparedStore] at compared
    have erasedEquality (bit : Bool) : Function.update (file input query key value result [] [bit] counter) 7 []=
        file input query key value result [] [] counter := by funext r;fin_cases r <;> simp [file]
    have erasedPending : Function.update (file input query key value result [true] [] counter) 5 []=
        file input query key value result [] [] counter := by funext r;fin_cases r <;> simp [file]
    have cost := Compare.preservingCost_le query key
    by_cases same : query=key
    · have truth : decide (query=key)=true := by simp [same]
      rw [truth] at compared
      have taken := takeValue_executes input query key value result counter
      have branched := branch_executes_true (7:Fin 13) takeValue (pushBit 5 true)
        (file input query key value result [] [true] counter)
        (file input query key [] value [false] [] counter) [] _ rfl
        ((erasedEquality true).symm ▸ taken)
      have combined := compared.sequence branched
      have ran := branch_executes_true (5:Fin 13) compareValue (pushBit 5 false)
        (file input query key value result [true] [] counter)
        (file input query key [] value [false] [] counter) [] _ rfl
        (erasedPending.symm ▸ combined)
      refine ⟨1+(Compare.preservingCost query key+1+(1+(result.length+6*value.length+8))),?_,?_⟩
      · omega
      · simpa [dispatch,same] using ran
    · have falsity : decide (query=key)=false := by simp [same]
      rw [falsity] at compared
      have pushed := pushBit_executes (5:Fin 13) true (file input query key value result [] [] counter)
      have pushStore : Function.update (file input query key value result [] [] counter) 5 [true]=
          file input query key value result [true] [] counter := by funext r;fin_cases r <;> simp [file]
      change Executes _ _ 1 (Function.update (file input query key value result [] [] counter) 5 [true]) at pushed
      rw [pushStore] at pushed
      have branched := branch_executes_false (7:Fin 13) takeValue (pushBit 5 true)
        (file input query key value result [] [false] counter)
        (file input query key value result [true] [] counter) [] 1 rfl
        ((erasedEquality false).symm ▸ pushed)
      have combined := compared.sequence branched
      have ran := branch_executes_true (5:Fin 13) compareValue (pushBit 5 false)
        (file input query key value result [true] [] counter)
        (file input query key value result [true] [] counter) [] _ rfl
        (erasedPending.symm ▸ combined)
      exact ⟨1+(Compare.preservingCost query key+1+(1+1)),by omega,
        by simpa [dispatch,same] using ran⟩

end Counting.StackMachine.AnchorFind
