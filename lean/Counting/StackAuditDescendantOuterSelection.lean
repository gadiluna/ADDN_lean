import Counting.StackAuditDescendantOuterLevel
import Counting.StackAuditDescendantOuterCheck
import Counting.AuditDescendantRange

namespace Counting.StackMachine.AuditDescendant
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

def checkSelected : Routine 46 := sequence outerLevel
  (branchRoutine 35 outerCheck (pushBit 35 true))

theorem checkSelected_executes (store : Store 46) (vista : Executable.Vista)
    (weights : Array Nat) (anchor last : Nat) (index : Fin vista.nodes.size) (steps : List Bool)
    (stepCount : steps.length=last-anchor)
    (source : store 46=(Encoding.array Encoding.node).encode vista.nodes)
    (weightsAt : store 32=(Encoding.array Encoding.natural).encode weights)
    (indexAt : (store 43).length=index.val)
    (anchorAt : store 40=anchor.bits) (lastAt : store 34=last.bits)
    (target : store 29=(index.val+1).bits) (stepBudget : store 38=steps)
    (empty : ∀ r : Fin 48,r.val<40 → r≠29 → r≠32 → r≠34 → r≠38 → store r=[]) :
    ∃ time ≤ 81000000000000*((store 46).length+(store 32).length+steps.length+anchor.size+last.size+1)^6,
      Executes checkSelected store time
        (Function.update store 35 [Executable.auditAncestor vista weights anchor last index.val]) := by
  obtain ⟨levelTime,levelBound,a⟩:=outerLevel_executes store vista index anchor source indexAt anchorAt (by
    intro r small
    apply empty r
    all_goals rcases small with small|rfl|rfl <;> simp_all
    all_goals omega)
  let selected:=decide ((vista.node index.val).level=anchor)
  let marked:=Function.update store 35 [selected]
  have restored : Function.update marked 35 []=store := by
    simp only [marked,Function.update_idem]
    rw [←empty 35 (by decide) (by decide) (by decide) (by decide) (by decide),Function.update_eq_self]
  let K:=(store 46).length+(store 32).length+steps.length+anchor.size+last.size+1
  have positive : 1 ≤ K := by dsimp only [K];omega
  have levelLimit : levelTime ≤ 12000*K^6 := levelBound.trans
    (Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left (by dsimp only [K];omega) 4).trans
      (Nat.pow_le_pow_right positive (by decide))))
  have one : 1 ≤ K^6:=Nat.one_le_pow _ _ positive
  by_cases matchLevel : (vista.node index.val).level=anchor
  · obtain ⟨checkTime,checkBound,b⟩:=outerCheck_executes store vista weights last index steps source weightsAt
      indexAt lastAt target stepBudget empty
    have same : Executable.auditAncestor vista weights anchor last index.val=
        decide (Executable.descendantCountRange vista steps.length last index.val 0 vista.nodes.size ≤
          weights[index.val]?.getD 0) := by
      simp only [Executable.auditAncestor,if_pos matchLevel,Executable.auditDescendantAt,stepCount]
    rw [←same] at b
    have branch:=branch_executes_true (35:Fin 48) outerCheck (pushBit 35 true) marked _ [] checkTime
      (by simp [marked,selected,matchLevel]) (by rw [restored];exact b)
    have checkLimit : checkTime ≤ 80000000000000*K^6 := checkBound.trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp only [K];omega) 6))
    refine ⟨_,?_,a.sequence branch⟩
    change levelTime+1+(1+checkTime) ≤ 81000000000000*K^6
    omega
  · have same : Executable.auditAncestor vista weights anchor last index.val=true := by
      simp [Executable.auditAncestor,matchLevel]
    rw [same]
    have b:=pushBit_executes (35:Fin 48) true store
    rw [empty 35 (by decide) (by decide) (by decide) (by decide) (by decide)] at b
    have branch:=branch_executes_false (35:Fin 48) outerCheck (pushBit 35 true) marked _ [] 1
      (by simp [marked,selected,matchLevel]) (by rw [restored];exact b)
    refine ⟨_,?_,a.sequence branch⟩
    change levelTime+1+(1+1) ≤ 81000000000000*K^6
    omega

end Counting.StackMachine.AuditDescendant
