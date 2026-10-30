import Counting.StackAuditPostSolverSizes

namespace Counting.StackMachine.AuditPostSolver
open Routine
set_option maxHeartbeats 1800000

def completeCoefficient : Nat := successCoefficient+1000000

theorem completeBudget_polynomial (vista : Executable.Vista) (candidate anchor : Nat) (values : Option (Array Rat))
    (fits : anchor≤vista.nodes.size) :
    completeBudget vista candidate anchor values ≤
      completeCoefficient*((inputWord vista candidate anchor values).length+1)^51 := by
  let S:=(inputWord vista candidate anchor values).length+1
  have positive : 1 ≤ S := by dsimp only [S];omega
  have inputSize : (inputWord vista candidate anchor values).length=
      2*candidate.size+1+(2*anchor.size+1)+(2*(Encoding.vista.encode vista).length+1)+
        (AuditPositive.inputWord values).length := by
    simp only [inputWord,List.length_append,Encoding.natural_length,Encoding.frame_length]
  have anchorBound : anchor.size ≤ S := by dsimp only [S];omega
  have codeBound : (Encoding.vista.encode vista).length ≤ S := by dsimp only [S];omega
  have candidateBase : (AuditCandidate.inputWord values candidate).length+1 ≤ S := by
    simp only [AuditCandidate.inputWord,List.length_append,Encoding.natural_length]
    dsimp only [S]
    omega
  have candidateBound:=Nat.mul_le_mul_left 500000 (Nat.pow_le_pow_left candidateBase 3)
  have one : 1 ≤ S^51 := Nat.one_le_pow _ _ positive
  have handleBound : handleBudget anchor vista (AuditCandidate.result values candidate) ≤
      (successCoefficient+2)*S^51 := by
    cases found : AuditCandidate.result values candidate with
    | none=>
      dsimp only [handleBudget]
      simp only [Nat.add_mul]
      omega
    | some natural=>
      have size:=candidate_some_length values candidate natural found
      have base : (AuditPropagation.propagationInputWord anchor vista natural).length+1 ≤ S := by
        simp only [AuditPropagation.propagationInputWord,AuditPropagation.propagationInputCodec,
          Encoding.product,Encoding.framed,List.length_append,Encoding.natural_length,Encoding.frame_length]
        dsimp only [S]
        omega
      have body:=successBudget_polynomial anchor vista natural fits
      have raised:=body.trans (Nat.mul_le_mul_left successCoefficient (Nat.pow_le_pow_left base 51))
      dsimp only [handleBudget]
      simp only [Nat.add_mul]
      omega
  have square : S^2 ≤ S^51 := Nat.pow_le_pow_right positive (by decide)
  have cubic : S^3 ≤ S^51 := Nat.pow_le_pow_right positive (by decide)
  have linear : S ≤ S^51 := Nat.le_self_pow (by decide) _
  change completeBudget vista candidate anchor values ≤ completeCoefficient*S^51
  dsimp only [completeBudget]
  change 100*S^2+500000*((AuditCandidate.inputWord values candidate).length+1)^3+
    handleBudget anchor vista (AuditCandidate.result values candidate)+
    2*(anchor.size+(Encoding.vista.encode vista).length+2)+3 ≤ completeCoefficient*S^51
  dsimp only [completeCoefficient]
  simp only [Nat.add_mul] at handleBound ⊢
  omega

theorem complete_polynomial (vista : Executable.Vista) (candidate anchor : Nat) (values : Option (Array Rat))
    (fits : anchor≤vista.nodes.size) (valid : vista.valid=true) :
    ∃ time ≤ completeCoefficient*((inputWord vista candidate anchor values).length+1)^51,
      Executes complete (inputStore 54 (inputWord vista candidate anchor values)) time
        (outputStore 54 (outputWord vista candidate anchor values)) := by
  obtain ⟨time,bounded,run⟩:=complete_executes vista candidate anchor values fits valid
  exact ⟨time,bounded.trans (completeBudget_polynomial vista candidate anchor values fits),run⟩

theorem complete_halts (vista : Executable.Vista) (candidate anchor : Nat) (values : Option (Array Rat))
    (fits : anchor≤vista.nodes.size) (valid : vista.valid=true) :
    ∃ time last,time ≤ completeCoefficient*((inputWord vista candidate anchor values).length+1)^51 ∧
      HaltsAt complete.program (inputWord vista candidate anchor values) time last ∧
      last.store 1=outputWord vista candidate anchor values := by
  obtain ⟨time,bounded,last,ran,halted,stored⟩:=complete_polynomial vista candidate anchor values fits valid
  exact ⟨time,last,bounded,⟨ran,halted⟩,by rw [stored];rfl⟩

end Counting.StackMachine.AuditPostSolver
