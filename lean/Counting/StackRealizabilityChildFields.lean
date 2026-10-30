import Counting.StackRealizabilitySelectedSum
import Counting.StackRealizabilityChildHeader

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def childSelectedRoles : Fin 10 ↪ Fin 27:=⟨![0,22,2,25,24,21,26,4,5,6],by decide⟩
def childFieldsSum : Routine 25:=mapRegisters childSelectedRoles selectedSum

def childContribution (node : Executable.Node) (target old value : Nat) : Nat:=
  if node.level=target ∧ node.parent=some old then value else 0

theorem parentCode_succ_iff (node : Executable.Node) (old : Nat) :
    DagValidation.parentCode node=old+1 ↔ node.parent=some old:=by
  cases parent:node.parent <;> simp [DagValidation.parentCode,parent]

theorem childFieldsSum_executes (store : Store 25) (node : Executable.Node)
    (target old value total : Nat)
    (level : store 0=node.level.bits) (parent : store 2=(DagValidation.parentCode node).bits)
    (targetInput : store 22=target.bits) (oldInput : store 25=(old+1).bits)
    (weight : store 24=value.bits) (accumulator : store 21=total.bits)
    (e4 : store 4=[]) (e5 : store 5=[]) (e6 : store 6=[]) (e26 : store 26=[]) :
    ∃ time ≤ 60*(node.level.size+target.size+(DagValidation.parentCode node).size+(old+1).size+
        value.size+total.size+1),
      Executes childFieldsSum store time
        (Function.update store 21 (total+childContribution node target old value).bits):=by
  let original : Store 8:=store ∘ childSelectedRoles
  have empty (r : Fin 10) (large : 6 ≤ r.val) : original r=[]:=by
    fin_cases r
    all_goals try norm_num at large
    all_goals simp [original,childSelectedRoles,e4,e5,e6,e26]
  obtain ⟨time,bound,ran⟩:=selectedSum_executes original empty
  have first : original 0=node.level.bits:=by simp [original,childSelectedRoles,level]
  have second : original 1=target.bits:=by simp [original,childSelectedRoles,targetInput]
  have third : original 2=(DagValidation.parentCode node).bits:=by simp [original,childSelectedRoles,parent]
  have fourth : original 3=(old+1).bits:=by simp [original,childSelectedRoles,oldInput]
  have fifth : original 4=value.bits:=by simp [original,childSelectedRoles,weight]
  have sixth : original 5=total.bits:=by simp [original,childSelectedRoles,accumulator]
  rw [first,second,third,fourth,fifth,sixth] at bound
  simp only [Encoding.bits_length] at bound
  have condition:=selectedSumCondition_naturals original node.level target (DagValidation.parentCode node)
    (old+1) first second third fourth
  simp only [parentCode_succ_iff] at condition
  rw [condition,fifth,sixth,Encoding.value_bits,Encoding.value_bits] at ran
  have final : (if decide (node.level=target ∧ node.parent=some old) then
      Function.update original 5 (total+value).bits else original)=
      Function.update original 5 (total+childContribution node target old value).bits:=by
    by_cases selected : node.level=target ∧ node.parent=some old
    · simp [selected,childContribution]
    · simp [selected,childContribution,←sixth]
  rw [final] at ran
  refine ⟨time,bound,?_⟩
  apply relocate_executes_frame selectedSum childSelectedRoles store _ original
    (Function.update original 5 (total+childContribution node target old value).bits) time rfl _ _ ran
  · intro r
    fin_cases r <;> simp [original,childSelectedRoles]
  · intro r outside
    have n21 : r≠21:=by intro same;subst r;exact outside 5 rfl
    simp [n21]

end Counting.StackMachine.RealizabilityCheck
