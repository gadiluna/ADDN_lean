import Counting.StackRealizabilitySelectedProduct
import Counting.StackRealizabilityChildFields

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

def supplyProductRoles : Fin 22 ↪ Fin 30:=
  ⟨![24,27,28,4,5,6,7,8,9,10,11,12,13,26,0,22,2,25,29,14,15,16],by decide⟩

def supplyFieldsSum : Routine 28:=mapRegisters supplyProductRoles selectedProduct

def supplyContribution (node : Executable.Node) (target old value : Nat) : Nat:=
  if node.level=target ∧ node.parent=some old then value*node.degree else 0

theorem supplyFieldsSum_executes (store : Store 28) (node : Executable.Node)
    (target old value total : Nat)
    (level : store 0=node.level.bits) (parent : store 2=(DagValidation.parentCode node).bits)
    (targetInput : store 22=target.bits) (oldInput : store 25=(old+1).bits)
    (weight : store 24=value.bits) (degree : store 27=node.degree.bits) (accumulator : store 26=total.bits)
    (work : ∀ r : Fin 30,4 ≤ r.val → r.val<17 → store r=[])
    (e28 : store 28=[]) (e29 : store 29=[]) :
    ∃ time ≤ 84000*(value.size+node.degree.size+total.size+node.level.size+target.size+
        (DagValidation.parentCode node).size+(old+1).size+1)^3,
      Executes supplyFieldsSum store time
        (Function.update store 26 (total+supplyContribution node target old value).bits):=by
  let original : Store 20:=store ∘ supplyProductRoles
  have empty (r : Fin 22) (member : (2 ≤ r.val ∧ r.val<13) ∨ 18 ≤ r.val) : original r=[]:=by
    fin_cases r
    all_goals try norm_num at member
    all_goals simp [original,supplyProductRoles,work,e28,e29]
  obtain ⟨time,bound,ran⟩:=selectedProduct_executes original empty
  have first : original 0=value.bits:=by simp [original,supplyProductRoles,weight]
  have second : original 1=node.degree.bits:=by simp [original,supplyProductRoles,degree]
  have totalAt : original 13=total.bits:=by simp [original,supplyProductRoles,accumulator]
  have levelAt : original 14=node.level.bits:=by simp [original,supplyProductRoles,level]
  have targetAt : original 15=target.bits:=by simp [original,supplyProductRoles,targetInput]
  have parentAt : original 16=(DagValidation.parentCode node).bits:=by simp [original,supplyProductRoles,parent]
  have oldAt : original 17=(old+1).bits:=by simp [original,supplyProductRoles,oldInput]
  rw [first,second,totalAt,levelAt,targetAt,parentAt,oldAt] at bound
  simp only [Encoding.bits_length] at bound
  have condition : selectedProductCondition original=decide (node.level=target ∧ node.parent=some old):=by
    apply Bool.eq_iff_iff.mpr
    simp only [selectedProductCondition,levelAt,targetAt,parentAt,oldAt,Encoding.bits_injective.eq_iff,
      Bool.and_eq_true,decide_eq_true_eq,parentCode_succ_iff]
  rw [condition,first,second,totalAt,Encoding.value_bits,Encoding.value_bits,Encoding.value_bits] at ran
  have final : (if decide (node.level=target ∧ node.parent=some old) then
      Function.update original 13 (total+value*node.degree).bits else original)=
      Function.update original 13 (total+supplyContribution node target old value).bits:=by
    by_cases selected : node.level=target ∧ node.parent=some old
    · simp [selected,supplyContribution]
    · simp [selected,supplyContribution,←totalAt]
  rw [final] at ran
  refine ⟨time,bound,?_⟩
  apply relocate_executes_frame selectedProduct supplyProductRoles store _ original
    (Function.update original 13 (total+supplyContribution node target old value).bits) time rfl _ _ ran
  · intro r
    fin_cases r <;> simp [original,supplyProductRoles]
  · intro r outside
    have n26 : r≠26:=by intro same;subst r;exact outside 13 rfl
    simp [n26]

end Counting.StackMachine.RealizabilityCheck
