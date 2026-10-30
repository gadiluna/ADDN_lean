import Counting.StackLexNatural
import Counting.StackUnframeCanonical

namespace Counting.StackMachine.Lexicographic
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def pairRoles : Fin 10 ↪ Fin 16 :=
  ⟨fun r=>⟨r.val,by omega⟩,by intro a b equal;exact Fin.ext (congrArg (fun r : Fin 16=>r.val) equal)⟩

def readPair : Routine 14 := sequence (ofProgram (unframeProgram 13 10 0 12))
  (sequence (ofProgram (unframeProgram 13 11 1 12)) (relocate pair pairRoles))

def readPairCost (left right : Nat) (unresolved : Bool) : Nat :=
  5*left.bits.length+5*right.bits.length+pairCost left.bits right.bits unresolved+6

def readPairResult (store : Store 14) (left right : Nat) (leftRest rightRest : List Bool)
    (unresolved answer : Bool) : Store 14 :=
  Function.update (Function.update (Function.update (Function.update store 10 leftRest) 11 rightRest)
    2 [unresolved && decide (left=right)])
    3 [if unresolved && !(decide (left=right)) then decide (left≤right) else answer]

/-- Read two framed canonical naturals and perform a numeric comparison.
The remaining serialized streams and every external register are retained. -/
theorem readPair_executes (store : Store 14) (left right : Nat) (leftRest rightRest : List Bool)
    (unresolved answer : Bool)
    (leftAt : store 10=Encoding.natural.encode left++leftRest)
    (rightAt : store 11=Encoding.natural.encode right++rightRest)
    (openAt : store 2=[unresolved]) (answerAt : store 3=[answer])
    (empty : ∀ r : Fin 16,r=0 ∨ r=1 ∨ (4≤r.val ∧ r.val≤9) ∨ r=12 → store r=[]) :
    Executes readPair store (readPairCost left right unresolved)
      (readPairResult store left right leftRest rightRest unresolved answer) := by
  have first := unframe_canonical_executes 13 (10:Fin 16) 0 12 (by decide) (by decide) (by decide)
    store left.bits leftRest leftAt (empty 12 (by simp))
  rw [empty 0 (by simp),List.append_nil] at first
  let firstRead := Function.update (Function.update store 10 leftRest) 0 left.bits
  have second := unframe_canonical_executes 13 (11:Fin 16) 1 12 (by decide) (by decide) (by decide)
    firstRead right.bits rightRest (by simp [firstRead,rightAt,Encoding.natural])
    (by simp [firstRead,empty])
  have secondEmpty : firstRead 1=[] := by simp [firstRead,empty]
  rw [secondEmpty,List.append_nil] at second
  let bothRead := Function.update (Function.update firstRead 11 rightRest) 1 right.bits
  let localStore : Store 8 := bothRead ∘ pairRoles
  have comparison := pair_naturals localStore left right unresolved answer
    (by simp [localStore,pairRoles,bothRead,firstRead])
    (by simp [localStore,pairRoles,bothRead])
    (by simp [localStore,pairRoles,bothRead,firstRead,openAt])
    (by simp [localStore,pairRoles,bothRead,firstRead,answerAt]) (by
      intro r lower
      fin_cases r <;> simp_all [localStore,pairRoles,bothRead,firstRead])
  have mapped : Executes (relocate pair pairRoles) bothRead
      (pairCost left.bits right.bits unresolved)
      (readPairResult store left right leftRest rightRest unresolved answer) := by
    apply relocate_executes_frame pair pairRoles bothRead _ localStore
      (naturalPairResult localStore left right unresolved answer) _ rfl _ _ comparison
    · intro r
      fin_cases r <;> simp [pairRoles,readPairResult,naturalPairResult,localStore,bothRead,firstRead,empty]
    · intro r outside
      have n0 : r≠0 := fun same=>outside 0 (by simpa [pairRoles] using same.symm)
      have n1 : r≠1 := fun same=>outside 1 (by simpa [pairRoles] using same.symm)
      have n2 : r≠2 := fun same=>outside 2 (by simpa [pairRoles] using same.symm)
      have n3 : r≠3 := fun same=>outside 3 (by simpa [pairRoles] using same.symm)
      by_cases r10 : r=10 <;> by_cases r11 : r=11 <;>
        simp [readPairResult,bothRead,firstRead,n0,n1,n2,n3,r10,r11]
  convert first.sequence (second.sequence mapped) using 1 <;>
    first | rfl | (dsimp only [readPairCost];omega)

theorem readPairCost_le (left right : Nat) (unresolved : Bool) :
    readPairCost left right unresolved≤13*(left.bits.length+right.bits.length)+44 := by
  have pairBound := pairCost_le left.bits right.bits unresolved
  unfold readPairCost
  omega

end Counting.StackMachine.Lexicographic
