import Counting.StackRealizabilityAccumulate
import Counting.StackNaturalCallMultiply

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

def weightedProductRoles : Fin 13 ↪ Fin 14 where
  toFun r:=⟨r.val,by omega⟩
  inj':=by intro a b same;apply Fin.ext;exact congrArg (fun r:Fin 14=>r.val) same

def weightedSumRoles : Fin 4 ↪ Fin 14:=⟨![13,2,3,4],by decide⟩

/-- Preserve both binary factors, add their product to register 13,
and restore all eleven private registers. -/
def weightedAccumulate : Routine 12:=sequence (mapRegisters weightedProductRoles NaturalCall.multiplicationRoutine)
  (accumulateAt weightedSumRoles)

theorem weightedAccumulate_executes (store : Store 12)
    (empty : ∀ r : Fin 14,2 ≤ r.val → r.val<13 → store r=[]) :
    ∃ time ≤ 83000*((store 0).length+(store 1).length+(store 13).length+1)^3,
      Executes weightedAccumulate store time
        (Function.update store 13
          (Encoding.value (store 13)+Encoding.value (store 0)*Encoding.value (store 1)).bits):=by
  obtain ⟨productTime,productBound,productRun⟩:=NaturalCall.multiplication_executes (store 0) (store 1)
  let product:=(Encoding.value (store 0)*Encoding.value (store 1)).bits
  let multiplied:=Function.update store 2 product
  have multiplying : Executes (mapRegisters weightedProductRoles NaturalCall.multiplicationRoutine)
      store productTime multiplied:=by
    apply relocate_executes_frame NaturalCall.multiplicationRoutine weightedProductRoles store multiplied
      (NaturalCall.file (store 0) (store 1) [] [] [] [] [])
      (NaturalCall.file (store 0) (store 1) product [] [] [] []) productTime _ _ _ productRun
    · funext r
      fin_cases r <;> simp [NaturalCall.file,weightedProductRoles,empty]
    · intro r
      fin_cases r <;> simp [NaturalCall.file,weightedProductRoles,multiplied,empty]
    · intro r outside
      have n2 : r≠2:=by intro same;subst r;exact outside 2 rfl
      simp [multiplied,n2]
  obtain ⟨sumTime,sumBound,summing⟩:=accumulateAt_executes weightedSumRoles multiplied
    (by simp [weightedSumRoles,multiplied,empty]) (by simp [weightedSumRoles,multiplied,empty])
  have left : multiplied (weightedSumRoles 0)=store 13:=by simp [multiplied,weightedSumRoles]
  have right : multiplied (weightedSumRoles 1)=product:=by simp [multiplied,weightedSumRoles]
  rw [left,right] at sumBound summing
  change Executes (accumulateAt weightedSumRoles) multiplied sumTime
    (Function.update (Function.update multiplied 13
      (Encoding.value (store 13)+Encoding.value product).bits) 2 []) at summing
  have productValue : Encoding.value product=Encoding.value (store 0)*Encoding.value (store 1):=
    Encoding.value_bits _
  rw [productValue] at summing
  have final : Function.update (Function.update multiplied 13
      (Encoding.value (store 13)+Encoding.value (store 0)*Encoding.value (store 1)).bits) 2 []=
      Function.update store 13
        (Encoding.value (store 13)+Encoding.value (store 0)*Encoding.value (store 1)).bits:=by
    funext r
    by_cases r2 : r=2 <;> by_cases r13 : r=13 <;> simp [multiplied,r2,r13,empty]
  rw [final] at summing
  have productLength:=NaturalCall.product_bits_length (store 0) (store 1)
  change product.length ≤ (store 0).length+(store 1).length at productLength
  let S:=(store 0).length+(store 1).length+(store 13).length+1
  have productLimit : productTime ≤ 82000*S^3:=by
    apply productBound.trans
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp only [S];omega) 3)
  have linear : S ≤ S^3:=Nat.le_self_pow (by decide) _
  have one : 1 ≤ S^3:=Nat.one_le_pow _ _ (by dsimp only [S];omega)
  exact ⟨_,by change _ ≤ 83000*S^3;dsimp only [S] at productLimit linear one ⊢;omega,
    multiplying.sequence summing⟩

def weightedAccumulateAt {registers : Nat} (roles : Fin 14 ↪ Fin (registers+2)) : Routine registers:=
  mapRegisters roles weightedAccumulate

theorem weightedAccumulateAt_executes {registers : Nat} (roles : Fin 14 ↪ Fin (registers+2))
    (store : Store registers) (empty : ∀ r : Fin 14,2 ≤ r.val → r.val<13 → store (roles r)=[]) :
    ∃ time ≤ 83000*((store (roles 0)).length+(store (roles 1)).length+(store (roles 13)).length+1)^3,
      Executes (weightedAccumulateAt roles) store time
        (Function.update store (roles 13)
          (Encoding.value (store (roles 13))+Encoding.value (store (roles 0))*Encoding.value (store (roles 1))).bits):=by
  obtain ⟨time,bound,run⟩:=weightedAccumulate_executes (store ∘ roles) empty
  refine ⟨time,bound,?_⟩
  apply relocate_executes_frame weightedAccumulate roles store _ (store ∘ roles)
    (Function.update (store ∘ roles) 13
      (Encoding.value (store (roles 13))+Encoding.value (store (roles 0))*Encoding.value (store (roles 1))).bits)
    time rfl _ _ run
  · intro r
    simp [Function.update,roles.injective.eq_iff]
  · intro r outside
    have other : r≠roles 13:=fun equal=>outside 13 equal.symm
    simp [other]

end Counting.StackMachine.RealizabilityCheck
