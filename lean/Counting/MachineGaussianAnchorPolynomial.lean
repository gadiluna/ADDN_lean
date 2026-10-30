import Counting.MachineGaussianLinearPolynomial
import Counting.GaussianLinearInputPhysical

namespace Counting.Machine
open Executable GaussianNormalMatrix StackMachine.GaussianCalls
set_option maxRecDepth 20000
set_option exponentiation.threshold 4000

variable {V : Type} [Fintype V]
variable (G : Nat  →  V  →  V  →  Nat) (leader : V  →  Bool)

/-- The complete rectangular solver on every actual anchor system takes
polynomially many physical TM transitions in population and binary label
length. Its input is the explicitly encoded anchor matrix. Building that
matrix from the DAG is a separate operation. -/
theorem gaussianAnchor_physical_clean (t : Nat) (observer : V) (vista : Vista)
    (valid : vista.valid=true) (depth : (vista.node vista.bottom).level=t)
    (physical : decodeNode vista t vista.bottom=Counting.history G leader t observer)
    (anchor leaders M : Nat) (mass : ∀ r,0 < r → r ≤ t → arcMass G r ≤ M) :
    let width := (levelNodes vista anchor).length
    let equations := anchorRows vista anchor leaders
    ∃ time output,
      time ≤  linearPhysicalCoefficient*
        (101*(Fintype.card V+1)^2*(M.size+leaders.size+3))^3000 ∧
      HaltsAt gaussianLinearProgram
        (StackMachine.GaussianNormal.inputWord width (equationMatrix width equations)) time output ∧
      output.tape.denotes=Turing.Tape.mk₁
        (((Encoding.optional Encoding.rationalRow).encode
          ((solveLinear? width equations).map Array.toList)).map bitSymbol) := by
  obtain ⟨time,output,bounded,halted,tape⟩ := gaussianAnchor_polynomial_clean vista anchor leaders
  have inputBound := GaussianLinearInputSize.physical_anchor_input_length G leader t observer vista valid depth physical anchor leaders M mass
  have positive : 1 ≤  (Fintype.card V+1)^2*(M.size+leaders.size+3) := by
    have left : 1 ≤  (Fintype.card V+1)^2 := Nat.one_le_pow' 2 (Fintype.card V)
    have right : 1 ≤  M.size+leaders.size+3 := by omega
    exact Nat.mul_le_mul left right
  have lengthBound :
      (StackMachine.GaussianNormal.inputWord (levelNodes vista anchor).length
        (equationMatrix (levelNodes vista anchor).length (anchorRows vista anchor leaders))).length+1 ≤ 
      101*(Fintype.card V+1)^2*(M.size+leaders.size+3) := by
    nlinarith only [inputBound,positive]
  exact ⟨time,output,bounded.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left lengthBound 3000)),halted,tape⟩

end Counting.Machine
