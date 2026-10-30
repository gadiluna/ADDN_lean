import Counting.StackRealizabilitySelectedProduct
import Counting.StackRealizabilityChildFields

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

def demandProductRoles : Fin 22 ↪ Fin 32:=
  ⟨![24,27,28,4,5,6,7,8,9,10,11,12,13,26,0,22,2,25,29,14,15,16],by decide⟩

def demandFieldsSum : Routine 30:=mapRegisters demandProductRoles selectedProduct

def demandContribution (level target source old value count : Nat) : Nat:=
  if level=target ∧ source=old then value*count else 0

theorem demandFieldsSum_executes (store : Store 30) (level target source old value count total : Nat)
    (levelInput : store 0=level.bits) (sourceInput : store 2=source.bits)
    (targetInput : store 22=target.bits) (oldInput : store 25=old.bits)
    (weight : store 24=value.bits) (countInput : store 27=count.bits) (accumulator : store 26=total.bits)
    (work : ∀ r : Fin 32,4 ≤ r.val → r.val<17 → store r=[])
    (e28 : store 28=[]) (e29 : store 29=[]) :
    ∃ time ≤ 84000*(value.size+count.size+total.size+level.size+target.size+
        source.size+old.size+1)^3,
      Executes demandFieldsSum store time
        (Function.update store 26 (total+demandContribution level target source old value count).bits):=by
  let original : Store 20:=store ∘ demandProductRoles
  have empty (r : Fin 22) (member : (2 ≤ r.val ∧ r.val<13) ∨ 18 ≤ r.val) : original r=[]:=by
    fin_cases r
    all_goals try norm_num at member
    all_goals simp [original,demandProductRoles,work,e28,e29]
  obtain ⟨time,bound,ran⟩:=selectedProduct_executes original empty
  have first : original 0=value.bits:=by simp [original,demandProductRoles,weight]
  have second : original 1=count.bits:=by simp [original,demandProductRoles,countInput]
  have totalAt : original 13=total.bits:=by simp [original,demandProductRoles,accumulator]
  have levelAt : original 14=level.bits:=by simp [original,demandProductRoles,levelInput]
  have targetAt : original 15=target.bits:=by simp [original,demandProductRoles,targetInput]
  have parentAt : original 16=source.bits:=by simp [original,demandProductRoles,sourceInput]
  have oldAt : original 17=old.bits:=by simp [original,demandProductRoles,oldInput]
  rw [first,second,totalAt,levelAt,targetAt,parentAt,oldAt] at bound
  simp only [Encoding.bits_length] at bound
  have condition : selectedProductCondition original=decide (level=target ∧ source=old):=by
    apply Bool.eq_iff_iff.mpr
    simp only [selectedProductCondition,levelAt,targetAt,parentAt,oldAt,Encoding.bits_injective.eq_iff,
      Bool.and_eq_true,decide_eq_true_eq]
  rw [condition,first,second,totalAt,Encoding.value_bits,Encoding.value_bits,Encoding.value_bits] at ran
  have final : (if decide (level=target ∧ source=old) then
      Function.update original 13 (total+value*count).bits else original)=
      Function.update original 13 (total+demandContribution level target source old value count).bits:=by
    by_cases selected : level=target ∧ source=old
    · simp [selected,demandContribution]
    · simp [selected,demandContribution,←totalAt]
  rw [final] at ran
  refine ⟨time,bound,?_⟩
  apply relocate_executes_frame selectedProduct demandProductRoles store _ original
    (Function.update original 13 (total+demandContribution level target source old value count).bits) time rfl _ _ ran
  · intro r
    fin_cases r <;> simp [original,demandProductRoles]
  · intro r outside
    have n26 : r≠26:=by intro same;subst r;exact outside 13 rfl
    simp [n26]

end Counting.StackMachine.RealizabilityCheck
