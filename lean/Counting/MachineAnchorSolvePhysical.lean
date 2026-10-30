import Counting.MachineAnchorSolve
import Counting.CountingSizeEncoding

namespace Counting.Machine
set_option exponentiation.threshold 10000
set_option maxRecDepth 131072
open Executable StackMachine.AnchorMatrix StackMachine.AnchorSolve

variable {V : Type} [Fintype V]
variable (G : Nat → V → V → Nat) (leader : V → Bool)

/-- End-to-end anchor solving from an actual shared DAG, including matrix
construction, exact elimination, original-equation checks and tape cleanup. -/
theorem anchorSolve_physical_clean (t : Nat) (observer : V) (vista : Vista)
    (valid : vista.valid=true) (depth : (vista.node vista.bottom).level=t)
    (physical : decodeNode vista t vista.bottom=Counting.history G leader t observer)
    (anchor leaders M : Nat) (mass : ∀ r,0<r → r≤t → arcMass G r≤M) :
    let n:=Fintype.card V
    let K:=(t+1)*n
    let B:=t+K+M.size+n+1
    ∃ time output,
      time ≤ (20*(polynomialCoefficient+59)^2)*(K*(8*B+9+n*(4*B+2))+2*anchor.size+2*leaders.size+5 )^9000 ∧
      HaltsAt anchorSolveProgram (inputWord anchor leaders vista) time output ∧
      output.tape.denotes=Turing.Tape.mk₁ ((resultWord vista anchor leaders).map bitSymbol) := by
  dsimp only
  obtain ⟨time,output,bounded,halted,tape⟩ := anchorSolve_clean vista anchor leaders
  have codeBound := Encoding.physical_vista_encoding_length G leader t observer vista valid depth physical M mass
  dsimp only at codeBound
  have inputBound : (inputWord anchor leaders vista).length+1 ≤
      (t+1)*Fintype.card V*(8*(t+(t+1)*Fintype.card V+M.size+Fintype.card V+1)+9+
        Fintype.card V*(4*(t+(t+1)*Fintype.card V+M.size+Fintype.card V+1)+2))+
          2*anchor.size+2*leaders.size+5 := by
    simp only [inputWord,List.length_append,Encoding.natural_length]
    omega
  exact ⟨time,output,bounded.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left inputBound 9000)),halted,tape⟩

end Counting.Machine
