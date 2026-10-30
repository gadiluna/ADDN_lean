import Counting.StackRealizabilitySelectedSum
import Counting.StackRealizabilityChildHeader

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def levelSelectedRoles : Fin 10 ↪ Fin 27:=⟨![0,22,2,25,24,21,26,4,5,6],by decide⟩
def levelFieldsSum : Routine 25:=mapRegisters levelSelectedRoles selectedSum

def levelContribution (node : Executable.Node) (target value : Nat) : Nat:=
  if node.level=target then value else 0

theorem levelFieldsSum_executes (store : Store 25) (node : Executable.Node)
    (target value total : Nat)
    (level : store 0=node.level.bits) (leftEmpty : store 2=[])
    (targetInput : store 22=target.bits) (rightEmpty : store 25=[])
    (weight : store 24=value.bits) (accumulator : store 21=total.bits)
    (e4 : store 4=[]) (e5 : store 5=[]) (e6 : store 6=[]) (e26 : store 26=[]) :
    ∃ time ≤ 60*(node.level.size+target.size+
        value.size+total.size+1),
      Executes levelFieldsSum store time
        (Function.update store 21 (total+levelContribution node target value).bits):=by
  let original : Store 8:=store ∘ levelSelectedRoles
  have empty (r : Fin 10) (large : 6 ≤ r.val) : original r=[]:=by
    fin_cases r
    all_goals try norm_num at large
    all_goals simp [original,levelSelectedRoles,e4,e5,e6,e26]
  obtain ⟨time,bound,ran⟩:=selectedSum_executes original empty
  have first : original 0=node.level.bits:=by simp [original,levelSelectedRoles,level]
  have second : original 1=target.bits:=by simp [original,levelSelectedRoles,targetInput]
  have third : original 2=(0:Nat).bits:=by simp [original,levelSelectedRoles,leftEmpty]
  have fourth : original 3=(0:Nat).bits:=by simp [original,levelSelectedRoles,rightEmpty]
  have fifth : original 4=value.bits:=by simp [original,levelSelectedRoles,weight]
  have sixth : original 5=total.bits:=by simp [original,levelSelectedRoles,accumulator]
  rw [first,second,third,fourth,fifth,sixth] at bound
  simp only [Encoding.bits_length,Nat.size_zero,Nat.add_zero] at bound
  have condition:=selectedSumCondition_naturals original node.level target 0 0 first second third fourth
  simp only [and_true] at condition
  rw [condition,fifth,sixth,Encoding.value_bits,Encoding.value_bits] at ran
  have final : (if decide (node.level=target) then
      Function.update original 5 (total+value).bits else original)=
      Function.update original 5 (total+levelContribution node target value).bits:=by
    by_cases selected : node.level=target
    · simp [selected,levelContribution]
    · simp [selected,levelContribution,←sixth]
  rw [final] at ran
  refine ⟨time,bound,?_⟩
  apply relocate_executes_frame selectedSum levelSelectedRoles store _ original
    (Function.update original 5 (total+levelContribution node target value).bits) time rfl _ _ ran
  · intro r
    fin_cases r <;> simp [original,levelSelectedRoles]
  · intro r outside
    have n21 : r≠21:=by intro same;subst r;exact outside 5 rfl
    simp [n21]

end Counting.StackMachine.RealizabilityCheck
