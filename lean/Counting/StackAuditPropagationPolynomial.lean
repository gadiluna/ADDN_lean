import Counting.StackAuditPropagationComplete
import Counting.StackAuditPropagationPreparedBounds
import Counting.AuditPropagationInputBounds

namespace Counting.StackMachine.AuditPropagation
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

def propagationCoefficient : Nat := 1000000000000000000000000000000000000000000000000000

/-- The input length pays for the stored DAG, binary anchor, all initial
weights, bounded counters, and every intermediate propagated array. -/
theorem propagationBudget_polynomial (anchor : Nat) (vista : Executable.Vista) (values : Array Nat)
    (fits : anchor ≤ vista.nodes.size) :
    propagationBudget anchor vista values ≤
      propagationCoefficient*((propagationInputWord anchor vista values).length+1)^32 := by
  let S := (propagationInputWord anchor vista values).length+1
  let table := Encoding.sequence Encoding.node vista.nodes.toList++Encoding.natural.encode vista.bottom
  have positive : 1 ≤ S := by dsimp only [S];omega
  have inputLength := propagationInput_length anchor vista values
  have codeBound : (Encoding.vista.encode vista).length ≤ S := by dsimp only [S];omega
  have nodeBound : vista.nodes.size ≤ S := (Encoding.vista_nodes_le_length vista).trans codeBound
  have bitsBound : anchor.size ≤ S := by dsimp only [S];omega
  have tableBound : table.length ≤ S := by
    have split : (Encoding.vista.encode vista).length=
        (Encoding.natural.encode vista.nodes.size).length+table.length := by
      simp only [table,Encoding.vista,Encoding.transport,Encoding.product,Encoding.list,
        List.length_append,Array.length_toList]
      omega
    omega
  have cube : S ≤ S^3 := Nat.le_self_pow (by decide) _
  have oneCube : 1 ≤ S^3 := Nat.one_le_pow _ _ positive
  have rounds : 1000*(vista.nodes.size+anchor.size+1)^3 ≤ 27000*S^3 := by
    have power := Nat.pow_le_pow_left (by omega : vista.nodes.size+anchor.size+1 ≤ 3*S) 3
    nlinarith only [power]
  have outputBound := propagateWeights_input_encoded_length anchor vista values fits
  change (propagationOutputWord anchor vista values).length ≤ 1080*S^3 at outputBound
  have cleanup : 10*((Encoding.vista.encode vista).length+table.length+2*vista.nodes.size+
      anchor.size+(propagationOutputWord anchor vista values).length+4) ≤ 10890*S^3 := by omega
  have prepared := preparedBudget_polynomial anchor vista values fits
  change preparedBudget anchor vista values ≤
    100000000000000000000000000000000000000000000000000*S^32 at prepared
  have raised : S^3 ≤ S^32 := Nat.pow_le_pow_right positive (by decide)
  have one32 : 1 ≤ S^32 := Nat.one_le_pow _ _ positive
  change propagationBudget anchor vista values ≤ propagationCoefficient*S^32
  dsimp only [propagationBudget]
  change 5000*S^3+1000*(vista.nodes.size+anchor.size+1)^3+preparedBudget anchor vista values+
    10*((Encoding.vista.encode vista).length+table.length+2*vista.nodes.size+
      anchor.size+(propagationOutputWord anchor vista values).length+4)+3 ≤ propagationCoefficient*S^32
  change _ ≤ 1000000000000000000000000000000000000000000000000000*S^32
  omega

theorem completePropagation_polynomial (anchor : Nat) (vista : Executable.Vista) (values : Array Nat)
    (fits : anchor ≤ vista.nodes.size) :
    ∃ time ≤ propagationCoefficient*((propagationInputWord anchor vista values).length+1)^32,
      Routine.Executes completePropagation (inputStore 42 (propagationInputWord anchor vista values)) time
        (outputStore 42 (propagationOutputWord anchor vista values)) := by
  obtain ⟨time,bounded,executed⟩ := completePropagation_executes anchor vista values fits
  exact ⟨time,bounded.trans (propagationBudget_polynomial anchor vista values fits),executed⟩

theorem completePropagation_halts (anchor : Nat) (vista : Executable.Vista) (values : Array Nat)
    (fits : anchor ≤ vista.nodes.size) :
    ∃ time last,time ≤ propagationCoefficient*((propagationInputWord anchor vista values).length+1)^32 ∧
      HaltsAt completePropagation.program (propagationInputWord anchor vista values) time last ∧
      last.store 1=propagationOutputWord anchor vista values := by
  obtain ⟨time,bounded,last,ran,halted,stored⟩ := completePropagation_polynomial anchor vista values fits
  exact ⟨time,last,bounded,⟨ran,halted⟩,by rw [stored];rfl⟩

end Counting.StackMachine.AuditPropagation
