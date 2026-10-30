import Counting.StackAuditBalanceComplete
import Counting.StackAuditBalanceBounds

namespace Counting.StackMachine.AuditBalance
open Routine
set_option maxHeartbeats 1600000

def balanceCoefficient : Nat := 100000000000000000000000000

theorem balanceBudget_polynomial (anchor : Nat) (vista : Executable.Vista) (weights : Array Nat)
    (fits : anchor ≤ vista.nodes.size) :
    balanceBudget anchor vista weights ≤
      balanceCoefficient*((balanceInputWord anchor vista weights).length+1)^17 := by
  let S:=(balanceInputWord anchor vista weights).length+1
  let table:=Encoding.sequence Encoding.node vista.nodes.toList++Encoding.natural.encode vista.bottom
  have positive : 1 ≤ S := by dsimp only [S];omega
  have inputSize : (balanceInputWord anchor vista weights).length=
      2*anchor.size+1+(2*(Encoding.vista.encode vista).length+1)+
        ((Encoding.array Encoding.natural).encode weights).length := by
    simp only [balanceInputWord,AuditPropagation.propagationInputWord,
      AuditPropagation.propagationInputCodec,Encoding.product,Encoding.framed,
      List.length_append,Encoding.natural_length,Encoding.frame_length]
    omega
  have codeBound : (Encoding.vista.encode vista).length ≤ S := by dsimp only [S];omega
  have weightsBound : ((Encoding.array Encoding.natural).encode weights).length ≤ S := by dsimp only [S];omega
  have nodes : vista.nodes.size ≤ S := (Encoding.vista_nodes_le_length vista).trans codeBound
  have anchorBits : anchor.size ≤ S := by dsimp only [S];omega
  have tableBound : table.length ≤ S := by
    have split : (Encoding.vista.encode vista).length=
        (Encoding.natural.encode vista.nodes.size).length+table.length := by
      simp only [table,Encoding.vista,Encoding.transport,Encoding.product,Encoding.list,
        List.length_append,Array.length_toList]
      omega
    omega
  have oldBits : (anchor-1).size ≤ anchor :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans (Nat.sub_le _ _)
  have newBits : (anchor-1+1).size ≤ anchor+1 :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
  have cleanup : balanceCleanupBudget anchor vista weights ≤ 60*S := by
    dsimp only [balanceCleanupBudget]
    change 6*((Encoding.vista.encode vista).length+((Encoding.array Encoding.natural).encode weights).length+
      table.length+vista.nodes.size+(anchor-1).size+(anchor-1+1).size+2) ≤ 60*S
    omega
  have rounds : 1200*(vista.nodes.size+anchor.size+1)^3 ≤ 32400*S^3 := by
    have raised:=Nat.pow_le_pow_left (by omega : vista.nodes.size+anchor.size+1 ≤ 3*S) 3
    nlinarith only [raised]
  have loop:=roundsBudget_polynomial anchor vista weights fits
  change roundsBudget vista weights 0 (anchor-1) ≤ 10000000000000000000000000*S^17 at loop
  have cube : S^3 ≤ S^17 := Nat.pow_le_pow_right positive (by decide)
  have linear : S ≤ S^17 := Nat.le_self_pow (by decide) _
  have one : 1 ≤ S^17 := Nat.one_le_pow _ _ positive
  change balanceBudget anchor vista weights ≤ balanceCoefficient*S^17
  dsimp only [balanceBudget]
  change 3000*S^3+1200*(vista.nodes.size+anchor.size+1)^3+roundsBudget vista weights 0 (anchor-1)+
    balanceCleanupBudget anchor vista weights+3 ≤ 100000000000000000000000000*S^17
  omega

theorem completeBalance_polynomial (anchor : Nat) (vista : Executable.Vista) (weights : Array Nat)
    (fits : anchor ≤ vista.nodes.size) (valid : vista.valid=true) (length : weights.size=vista.nodes.size) :
    ∃ time ≤ balanceCoefficient*((balanceInputWord anchor vista weights).length+1)^17,
      Executes completeBalance (inputStore 48 (balanceInputWord anchor vista weights)) time
        (outputStore 48 [Executable.auditBalance vista weights anchor]) := by
  obtain ⟨time,bounded,run⟩:=completeBalance_executes anchor vista weights fits valid length
  exact ⟨time,bounded.trans (balanceBudget_polynomial anchor vista weights fits),run⟩

theorem completeBalance_halts (anchor : Nat) (vista : Executable.Vista) (weights : Array Nat)
    (fits : anchor ≤ vista.nodes.size) (valid : vista.valid=true) (length : weights.size=vista.nodes.size) :
    ∃ time last,time ≤ balanceCoefficient*((balanceInputWord anchor vista weights).length+1)^17 ∧
      HaltsAt completeBalance.program (balanceInputWord anchor vista weights) time last ∧
      last.store 1=[Executable.auditBalance vista weights anchor] := by
  obtain ⟨time,bounded,last,run,halted,stored⟩:=completeBalance_polynomial anchor vista weights fits valid length
  exact ⟨time,last,bounded,⟨run,halted⟩,by rw [stored];rfl⟩

end Counting.StackMachine.AuditBalance
