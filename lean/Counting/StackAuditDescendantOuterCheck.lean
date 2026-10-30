import Counting.StackAuditDescendantPreserving
import Counting.StackAuditDescendantQuery

namespace Counting.StackMachine.AuditDescendant
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

def outerCheck : Routine 46 := sequence prepareQuery (sequence preservingCheck (clear 33))

/-- For a real outer-loop index, construct its query, run the entire
descendant inequality and restore the query workspace for the next item. -/
theorem outerCheck_executes (store : Store 46) (vista : Executable.Vista)
    (weights : Array Nat) (last : Nat) (index : Fin vista.nodes.size) (steps : List Bool)
    (source : store 46=(Encoding.array Encoding.node).encode vista.nodes)
    (weightsAt : store 32=(Encoding.array Encoding.natural).encode weights)
    (indexAt : (store 43).length=index.val)
    (lastAt : store 34=last.bits) (target : store 29=(index.val+1).bits)
    (stepBudget : store 38=steps)
    (empty : ∀ r : Fin 48,r.val<40 → r≠29 → r≠32 → r≠34 → r≠38 → store r=[]) :
    ∃ time ≤ 80000000000000*((store 46).length+(store 32).length+steps.length+last.size+1)^6,
      Executes outerCheck store time
        (Function.update store 35 [decide (Executable.descendantCountRange vista steps.length last index.val
          0 vista.nodes.size ≤ weights[index.val]?.getD 0)]) := by
  obtain ⟨queryTime,queryBound,a⟩:=prepareQuery_executes store
    (empty 0 (by decide) (by decide) (by decide) (by decide) (by decide))
    (empty 18 (by decide) (by decide) (by decide) (by decide) (by decide))
    (empty 31 (by decide) (by decide) (by decide) (by decide) (by decide))
    (empty 33 (by decide) (by decide) (by decide) (by decide) (by decide))
  rw [indexAt] at a queryBound
  let queried:=Function.update store 33 (Encoding.natural.encode index.val)
  obtain ⟨checkTime,checkBound,b⟩:=preservingCheck_executes queried vista weights last index.val steps
    (by simp [queried,source]) (by simp [queried,weightsAt]) (by simp [queried])
    (by simp [queried,lastAt]) (by simp [queried,target]) (by simp [queried,stepBudget]) (by
      intro r small n29 n32 n33 n34 n38
      simp [queried,n33,empty r small n29 n32 n34 n38])
  let answer:=decide (Executable.descendantCountRange vista steps.length last index.val 0 vista.nodes.size ≤
    weights[index.val]?.getD 0)
  let checked:=Function.update queried 35 [answer]
  have c:=clear_executes (33:Fin 48) checked
  have queryAt : checked 33=Encoding.natural.encode index.val := by simp [checked,queried]
  rw [queryAt,Encoding.natural_length] at c
  have final : Function.update checked 33 []=Function.update store 35 [answer] := by
    funext r
    by_cases r33:r=33 <;> by_cases r35:r=35 <;> simp [checked,queried,r33,r35,empty]
  rw [final] at c
  have tableAt : (queried 46).length=(store 46).length := by simp [queried]
  have weightsSame : (queried 32).length=(store 32).length := by simp [queried]
  have querySize : (queried 33).length=2*index.val.size+1 := by simp [queried,Encoding.natural_length]
  rw [tableAt,weightsSame,querySize] at checkBound
  have nodes : vista.nodes.size ≤ (store 46).length := by
    rw [source]
    exact Encoding.array_size_le_length _ _ (by intro node _;exact Encoding.node_positive_length node)
  have indexBound:=index.isLt
  have width : index.val.size ≤ index.val:=Nat.size_le.mpr Nat.lt_two_pow_self
  have codeWidth : (index.val+1).size ≤ index.val+1:=Nat.size_le.mpr Nat.lt_two_pow_self
  let K:=(store 46).length+(store 32).length+steps.length+last.size+1
  have positive : 1 ≤ K := by dsimp only [K];omega
  have factor : (store 46).length+(store 32).length+(2*index.val.size+1)+steps.length+
      (index.val+1).size+last.size+1 ≤ 4*K := by dsimp only [K];omega
  have scaled:=checkBound.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left factor 6))
  have checkLimit : checkTime ≤ 77824000000000*K^6 := by nlinarith only [scaled]
  have small : index.val+1 ≤ K := by dsimp only [K];omega
  have queryLimit : queryTime ≤ 20*K^2 := queryBound.trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left small 2))
  have square : K^2 ≤ K^6:=Nat.pow_le_pow_right positive (by decide)
  have linear : K ≤ K^6:=Nat.le_self_pow (by decide) _
  have one : 1 ≤ K^6:=Nat.one_le_pow _ _ positive
  refine ⟨_,?_,a.sequence (b.sequence c)⟩
  change queryTime+1+(checkTime+1+(2*index.val.size+1+1)) ≤ 80000000000000*K^6
  omega

end Counting.StackMachine.AuditDescendant
