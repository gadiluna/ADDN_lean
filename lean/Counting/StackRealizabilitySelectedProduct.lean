import Counting.StackRealizabilityWeightedAccumulate
import Counting.StackRealizabilitySelectedSum

namespace Counting.StackMachine.RealizabilityCheck
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

def selectedProductRoles : Fin 14 ↪ Fin 22 where
  toFun r:=⟨r.val,by omega⟩
  inj':=by intro a b same;apply Fin.ext;exact congrArg (fun r:Fin 22=>r.val) same

def selectedProductFirst : Fin 6 ↪ Fin 22:=⟨![14,15,18,19,20,21],by decide⟩
def selectedProductSecond : Fin 6 ↪ Fin 22:=⟨![16,17,18,19,20,21],by decide⟩

def selectedProduct : Routine 20:=sequence (Compare.preservingEquality 16 selectedProductFirst)
  (sequence (Compare.preservingEquality 16 selectedProductSecond)
    (sequence (ofProgram (combineFlagsProgram 20 18))
      (branchRoutine 18 (weightedAccumulateAt selectedProductRoles) (skip 20))))

def selectedProductCondition (store : Store 20) : Bool:=
  decide (store 14=store 15) && decide (store 16=store 17)

theorem selectedProduct_executes (store : Store 20)
    (empty : ∀ r : Fin 22,(2 ≤ r.val ∧ r.val<13) ∨ 18 ≤ r.val → store r=[]) :
    ∃ time ≤ 84000*((store 0).length+(store 1).length+(store 13).length+(store 14).length+
        (store 15).length+(store 16).length+(store 17).length+1)^3,
      Executes selectedProduct store time
        (if selectedProductCondition store then Function.update store 13
          (Encoding.value (store 13)+Encoding.value (store 0)*Encoding.value (store 1)).bits else store):=by
  let first:=decide (store 14=store 15)
  let second:=decide (store 16=store 17)
  have firstRun:=Compare.preservingEquality_executes 16 selectedProductFirst store
    (empty 19 (by decide)) (empty 20 (by decide)) (empty 21 (by decide))
  change Executes (Compare.preservingEquality 16 selectedProductFirst) store
    (Compare.preservingCost (store 14) (store 15)) (Function.update store 18 (first::store 18)) at firstRun
  rw [empty 18 (by decide)] at firstRun
  let firstStore:=Function.update store 18 [first]
  have secondRun:=Compare.preservingEquality_executes 16 selectedProductSecond firstStore
    (by simp [selectedProductSecond,firstStore,empty])
    (by simp [selectedProductSecond,firstStore,empty])
    (by simp [selectedProductSecond,firstStore,empty])
  change Executes (Compare.preservingEquality 16 selectedProductSecond) firstStore
    (Compare.preservingCost (firstStore 16) (firstStore 17))
      (Function.update firstStore 18 (decide (firstStore 16=firstStore 17)::firstStore 18)) at secondRun
  have secondResult : Function.update firstStore 18 (decide (firstStore 16=firstStore 17)::firstStore 18)=
      Function.update store 18 [second,first]:=by simp [firstStore,second]
  rw [secondResult] at secondRun
  have secondLeft : firstStore 16=store 16:=by simp [firstStore]
  have secondRight : firstStore 17=store 17:=by simp [firstStore]
  rw [secondLeft,secondRight] at secondRun
  let bothStore:=Function.update store 18 [second,first]
  have combining:=combineFlags_executes 20 18 bothStore first second [] (by simp [bothStore])
  have combinedStore : Function.update bothStore 18 [first&&second]=Function.update store 18 [first&&second]:=by
    simp [bothStore]
  rw [combinedStore] at combining
  let checked:=Function.update store 18 [first&&second]
  have restored : Function.update checked 18 []=store:=by
    simp only [checked,Function.update_idem,←empty 18 (by decide),Function.update_eq_self]
  have firstCost:=Compare.preservingCost_le (store 14) (store 15)
  have secondCost:=Compare.preservingCost_le (store 16) (store 17)
  let S:=(store 0).length+(store 1).length+(store 13).length+(store 14).length+
    (store 15).length+(store 16).length+(store 17).length+1
  have linear : S ≤ S^3:=Nat.le_self_pow (by decide) _
  have one : 1 ≤ S^3:=Nat.one_le_pow _ _ (by dsimp only [S];omega)
  by_cases selected : (first&&second)=true
  · have workspace (r : Fin 14) (lo : 2 ≤ r.val) (hi : r.val<13) : store (selectedProductRoles r)=[]:=
      empty (selectedProductRoles r) (Or.inl ⟨lo,hi⟩)
    obtain ⟨bodyTime,bodyBound,bodyRun⟩:=weightedAccumulateAt_executes selectedProductRoles store workspace
    change bodyTime ≤ 83000*((store 0).length+(store 1).length+(store 13).length+1)^3 at bodyBound
    change Executes (weightedAccumulateAt selectedProductRoles) store bodyTime
      (Function.update store 13
        (Encoding.value (store 13)+Encoding.value (store 0)*Encoding.value (store 1)).bits) at bodyRun
    have branched:=branch_executes_true (18:Fin 22) (weightedAccumulateAt selectedProductRoles) (skip 20) checked
      _ [] bodyTime (by simp [checked,selected]) (by rw [restored];exact bodyRun)
    have condition : selectedProductCondition store=true:=selected
    rw [condition]
    have bodyLimit : bodyTime ≤ 83000*S^3:=by
      apply bodyBound.trans
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp only [S];omega) 3)
    refine ⟨_,?_,firstRun.sequence (secondRun.sequence (combining.sequence branched))⟩
    change _ ≤ 84000*S^3
    dsimp only [S] at bodyLimit linear one ⊢
    omega
  · have condition : (first&&second)=false:=Bool.eq_false_iff.mpr selected
    have branched:=branch_executes_false (18:Fin 22) (weightedAccumulateAt selectedProductRoles) (skip 20) checked
      store [] 0 (by simp [checked,condition]) (by rw [restored];exact Routine.skip_executes store)
    have failed : selectedProductCondition store=false:=condition
    rw [failed]
    refine ⟨_,?_,firstRun.sequence (secondRun.sequence (combining.sequence branched))⟩
    change _ ≤ 84000*S^3
    dsimp only [S] at linear one ⊢
    omega

end Counting.StackMachine.RealizabilityCheck
