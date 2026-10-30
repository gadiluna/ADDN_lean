import Counting.StackAuditDescendantLoop

namespace Counting.StackMachine.AuditDescendant
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def countAll : Routine 38 := sequence (pushBit 37 true)
  (sequence countLoop (sequence (clear 36) (clear 37)))

/-- Count all matching descendants using exactly the supplied table-size
budget. Both per-node index representations are created and cleared by
the program, and the complete accumulated unary result is bounded by the
number of stored nodes. Header extraction is a separate charged stage. -/
theorem countAll_executes (store : Store 38) (vista : Executable.Vista)
    (last ancestor : Nat) (steps bits : List Bool)
    (count : bits.length=vista.nodes.size)
    (source : store 17=Encoding.sequence Encoding.node vista.nodes.toList)
    (lastAt : store 34=last.bits) (target : store 29=(ancestor+1).bits)
    (stepBudget : store 38=steps) (counter : store 30=bits)
    (e35 : store 35=[]) (e36 : store 36=[]) (e37 : store 37=[])
    (empty : ∀ r : Fin 40,r.val ≤ 28 → r≠17 → store r=[]) :
    ∃ time ≤ 16000000000*((store 17).length+steps.length+(ancestor+1).size+last.size+1)^6,
      Executes countAll store time
        (Function.update (Function.update store 30 []) 39
          (List.replicate (Executable.descendantCountRange vista steps.length last ancestor 0 vista.nodes.size) true++store 39)) := by
  have a:=pushBit_executes (37:Fin 40) true store
  rw [e37] at a
  let ready:=Function.update store 37 [true]
  obtain ⟨loopTime,loopBound,b⟩:=countLoop_executes ready vista 0 last ancestor steps bits
    (by omega) (by simp [ready,source]) (by simp [ready,e36]) (by simp [ready,Nat.bits])
    (by simp [ready,lastAt]) (by simp [ready,target]) (by simp [ready,stepBudget])
    (by simp [ready,counter]) (by simp [ready,e35]) (by
      intro r small different
      have n37 : r≠37 := by intro same;subst r;norm_num at small
      simp [ready,n37,empty r small different])
  let counted:=countLoopResult ready vista steps.length last ancestor 0 bits.length
  have c:=clear_executes (36:Fin 40) counted
  have indexLength : (counted 36).length=vista.nodes.size := by
    simp [counted,countLoopResult,ready,e36,count]
  rw [indexLength] at c
  let cleared:=Function.update counted 36 []
  have d:=clear_executes (37:Fin 40) cleared
  have codeLength : (cleared 37).length=(vista.nodes.size+1).size := by
    simp [cleared,counted,countLoopResult,count,Encoding.bits_length]
  rw [codeLength] at d
  have final : Function.update cleared 37 []=Function.update (Function.update store 30 []) 39
      (List.replicate (Executable.descendantCountRange vista steps.length last ancestor 0 vista.nodes.size) true++store 39) := by
    funext r
    by_cases r30:r=30 <;> by_cases r36:r=36 <;> by_cases r37:r=37 <;> by_cases r39:r=39 <;>
      simp [cleared,counted,countLoopResult,ready,r30,r36,r37,r39,count,e36,e37]
  rw [final] at d
  refine ⟨_,?_,a.sequence (b.sequence (c.sequence d))⟩
  have sourceSame : (ready 17).length=(store 17).length := by simp [ready]
  rw [sourceSame,count] at loopBound
  let K:=(store 17).length+steps.length+(ancestor+1).size+last.size+1
  have nodes:=DagValidation.node_sequence_count_le vista.nodes.toList
  rw [Array.length_toList,←source] at nodes
  have nodeBound : vista.nodes.size ≤ K := by dsimp only [K];omega
  have codeBound : (vista.nodes.size+1).size ≤ K := by
    have size : (vista.nodes.size+1).size ≤ vista.nodes.size+1 := Nat.size_le.mpr Nat.lt_two_pow_self
    dsimp only [K];omega
  have multiplied:=Nat.mul_le_mul_right (15000000000*K^5+2) nodeBound
  have power : K*K^5=K^6 := by ring
  have linear : K ≤ K^6:=Nat.le_self_pow (by decide) _
  have one : 1 ≤ K^6:=Nat.one_le_pow _ _ (by dsimp only [K];omega)
  change loopTime ≤ vista.nodes.size*(15000000000*K^5+2)+1 at loopBound
  change 1+1+(loopTime+1+((vista.nodes.size+1)+1+((vista.nodes.size+1).size+1))) ≤ 16000000000*K^6
  nlinarith only [loopBound,multiplied,power,linear,one,nodeBound,codeBound]

end Counting.StackMachine.AuditDescendant
