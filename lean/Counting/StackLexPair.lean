import Counting.StackLexFlags
import Counting.StackBinaryComparePreserving
import Counting.StackBinaryCompareBits
import Counting.StackCompare
import Counting.StackRegisterFrames

namespace Counting.StackMachine.Lexicographic
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def comparisonRoles : Fin 6 ↪ Fin 10 := ⟨![0,1,5,7,8,9],by decide⟩
def settleRoles : Fin 8 ↪ Fin 10 :=
  ⟨fun r=>⟨r.val,by omega⟩,by intro a b equal;exact Fin.ext (congrArg (fun r : Fin 10=>r.val) equal)⟩

def pair : Routine 8 := sequence (Binary.preservingComparison 4 comparisonRoles)
  (sequence (ofProgram (Compare.equalityProgram 8 0 1 4)) (relocate settle settleRoles))

def pairCost (left right : List Bool) (unresolved : Bool) : Nat :=
  Binary.preservingCompareCost left right+Compare.equalityCost left right+
    settleCost unresolved (decide (left=right))+2

def pairResult (store : Store 8) (left right : List Bool) (unresolved answer : Bool) : Store 8 :=
  Function.update (Function.update (Function.update (Function.update store 0 []) 1 [])
    2 [unresolved && decide (left=right)])
    3 [if unresolved && !(decide (left=right)) then Binary.compareBits true left right else answer]

/-- One pair of binary naturals is compared physically, and its equality
and order flags feed the first-difference controller. -/
theorem pair_executes (store : Store 8) (unresolved answer : Bool)
    (openAt : store 2=[unresolved]) (answerAt : store 3=[answer])
    (empty : ∀ r : Fin 10,4 ≤ r.val → store r=[]) :
    Executes pair store (pairCost (store 0) (store 1) unresolved)
      (pairResult store (store 0) (store 1) unresolved answer) := by
  let left := store 0
  let right := store 1
  let leFlag := Binary.compareBits true left right
  let eqFlag := decide (left=right)
  have comparison := Binary.preservingComparison_executes 4 comparisonRoles store
    (empty 7 (by decide)) (empty 8 (by decide)) (empty 9 (by decide))
  have flagEmpty : store (comparisonRoles 2)=[] := empty 5 (by decide)
  rw [flagEmpty] at comparison
  let compared := Function.update store 5 [leFlag]
  change Executes (Binary.preservingComparison 4 comparisonRoles) store
    (Binary.preservingCompareCost left right) compared at comparison
  have equality := Compare.equality_executes 8 (0:Fin 10) 1 4 (by decide) (by decide) (by decide) compared
  have leftAt : compared 0=left := by simp [compared,left]
  have rightAt : compared 1=right := by simp [compared,right]
  have equalEmpty : compared 4=[] := by simp [compared,empty]
  rw [leftAt,rightAt,equalEmpty] at equality
  let equalized := Function.update (Function.update (Function.update compared 0 []) 1 []) 4 [eqFlag]
  let localStore : Store 6 := equalized ∘ settleRoles
  have settling := settle_executes localStore unresolved answer eqFlag leFlag
    (by simp [localStore,settleRoles,equalized,compared,openAt])
    (by simp [localStore,settleRoles,equalized,compared,answerAt])
    (by simp [localStore,settleRoles,equalized])
    (by simp [localStore,settleRoles,equalized,compared])
    (by simp [localStore,settleRoles,equalized,compared,empty])
  have relocated : Executes (relocate settle settleRoles) equalized
      (settleCost unresolved eqFlag) (pairResult store left right unresolved answer) := by
    apply relocate_executes_frame settle settleRoles equalized _ localStore
      (settled localStore unresolved answer eqFlag leFlag) _ rfl _ _ settling
    · intro r
      fin_cases r <;> simp [settleRoles,settled,localStore,equalized,compared,pairResult,eqFlag,leFlag,empty]
    · intro r outside
      have n0 : r≠0 := fun equal=>outside 0 (by simpa [settleRoles] using equal.symm)
      have n1 : r≠1 := fun equal=>outside 1 (by simpa [settleRoles] using equal.symm)
      have n2 : r≠2 := fun equal=>outside 2 (by simpa [settleRoles] using equal.symm)
      have n3 : r≠3 := fun equal=>outside 3 (by simpa [settleRoles] using equal.symm)
      have n4 : r≠4 := fun equal=>outside 4 (by simpa [settleRoles] using equal.symm)
      have n5 : r≠5 := fun equal=>outside 5 (by simpa [settleRoles] using equal.symm)
      simp [pairResult,equalized,compared,n0,n1,n2,n3,n4,n5]
  convert comparison.sequence (equality.sequence relocated) using 1 <;>
    first | rfl | (dsimp only [pairCost,eqFlag,left,right];omega)

theorem pairCost_le (left right : List Bool) (unresolved : Bool) :
    pairCost left right unresolved ≤ 8*(left.length+right.length)+38 := by
  have first := Binary.preservingCompareCost_le left right
  have second := Compare.equalityCost_le left right
  have third := settleCost_le unresolved (decide (left=right))
  unfold pairCost
  omega

end Counting.StackMachine.Lexicographic
