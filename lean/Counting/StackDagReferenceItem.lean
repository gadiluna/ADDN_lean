import Counting.StackDagDistinctGuard
import Counting.StackDagRedItem

/-! A reference scan reads each incoming source index in binary and accumulates
inequality with one target. Counts are parsed and discarded without expansion. -/
namespace Counting.StackMachine.DagValidation
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

def referencePairRoles : Fin 5 ↪ Fin 35:=⟨![28,22,31,4,1],by decide⟩
def referenceCompareRoles : Fin 6 ↪ Fin 35:=⟨![22,26,1,2,3,4],by decide⟩

def referenceItem : Routine 33:=sequence (pairRoutine 30 referencePairRoles)
  (sequence (ofProgram (combineFlagsProgram 33 1))
    (sequence (distinctGuard 29 referenceCompareRoles) (sequence (clear 22) (clear 31))))

def referenceItemStore (store : Store 33) (accepted : Bool) (tail : List Bool)
    (target : Nat) (edge : Nat×Nat) (suffix : List Bool) : Store 33:=
  Function.update (Function.update store 28 suffix) 1 ((accepted && decide (edge.1≠target))::tail)

theorem referenceItem_executes (store : Store 33) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (e2 : store 2=[]) (e3 : store 3=[]) (e4 : store 4=[]) (e22 : store 22=[]) (e31 : store 31=[])
    (target : Nat) (targetCode : store 26=target.bits)
    (edge : Nat×Nat) (suffix : List Bool)
    (input : store 28=(Encoding.product Encoding.natural Encoding.natural).encode edge++suffix) :
    ∃ time ≤ 50*((store 28).length+target.size+1),
      Executes referenceItem store time (referenceItemStore store accepted tail target edge suffix) := by
  obtain ⟨pairTime,pairBound,pairRun⟩:=pair_executes 30 referencePairRoles referencePairRoles.injective store e4
  rw [pair_result_spec 30 referencePairRoles referencePairRoles.injective] at pairRun
  have parsed : parsePair (store 28)=⟨edge.1.bits,edge.2.bits,suffix,true⟩:=by
    rw [input]
    exact parsePair_frames _ _ _
  let parsedStore:=Function.update (Function.update (Function.update (Function.update store 28 suffix)
    22 edge.1.bits) 31 edge.2.bits) 1 (true::accepted::tail)
  have parsedEq : pairExpected 30 referencePairRoles store=parsedStore:=by
    funext r
    fin_cases r <;> simp [pairExpected,referencePairRoles,parsed,parsedStore,status,e2,e3,e4,e22,e31]
  rw [parsedEq] at pairRun
  have combined:=combineFlags_executes 33 1 parsedStore accepted true tail (by simp [parsedStore])
  let joined:=Function.update parsedStore 1 (accepted::tail)
  have combinedRun : Executes (ofProgram (combineFlagsProgram 33 1)) parsedStore 3 joined:=by
    simpa only [Bool.and_true] using combined
  have compared:=distinctGuard_executes 29 referenceCompareRoles joined accepted tail
    (by simp [referenceCompareRoles,joined]) (by simp [referenceCompareRoles,joined,parsedStore,e2])
    (by simp [referenceCompareRoles,joined,parsedStore,e3]) (by simp [referenceCompareRoles,joined,parsedStore,e4])
  have predicate : (!decide (joined (referenceCompareRoles 0)=joined (referenceCompareRoles 1)))=decide (edge.1≠target):=by
    simp [referenceCompareRoles,joined,parsedStore,targetCode,Encoding.bits_injective.eq_iff]
  rw [predicate] at compared
  let checked:=Function.update joined 1 ((accepted && decide (edge.1≠target))::tail)
  have clearIndex:=clear_executes (22:Fin 35) checked
  have indexValue : checked 22=edge.1.bits:=by simp [checked,joined,parsedStore]
  rw [indexValue] at clearIndex
  let middle:=Function.update checked 22 []
  have clearCount:=clear_executes (31:Fin 35) middle
  have countValue : middle 31=edge.2.bits:=by simp [middle,checked,joined,parsedStore]
  rw [countValue] at clearCount
  have final : Function.update middle 31 []=referenceItemStore store accepted tail target edge suffix:=by
    funext r
    by_cases r1 : r=1 <;> by_cases r22 : r=22 <;> by_cases r28 : r=28 <;> by_cases r31 : r=31 <;>
      simp [referenceItemStore,middle,checked,joined,parsedStore,r1,r22,r28,r31,e22,e31]
  rw [final] at clearCount
  have first : joined (referenceCompareRoles 0)=edge.1.bits:=by simp [referenceCompareRoles,joined,parsedStore]
  have second : joined (referenceCompareRoles 1)=target.bits:=by simp [referenceCompareRoles,joined,parsedStore,targetCode]
  have comparison:=Compare.preservingCost_le (joined (referenceCompareRoles 0)) (joined (referenceCompareRoles 1))
  rw [first,second,Encoding.bits_length,Encoding.bits_length] at comparison
  have inputLength : edge.1.size+edge.2.size≤(store 28).length:=by
    rw [input]
    simp only [Encoding.product,List.length_append,Encoding.natural_length]
    omega
  change pairTime≤6*(store 28).length+13 at pairBound
  refine ⟨_,?_,pairRun.sequence (combinedRun.sequence (compared.sequence (clearIndex.sequence clearCount)))⟩
  rw [first,second,Encoding.bits_length,Encoding.bits_length]
  omega

end Counting.StackMachine.DagValidation
