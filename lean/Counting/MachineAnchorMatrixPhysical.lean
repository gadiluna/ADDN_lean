import Counting.MachineAnchorMatrix
import Counting.CountingSizeEncoding

namespace Counting.Machine
open Executable StackMachine.AnchorMatrix

variable {V : Type} [Fintype V]
variable (G : Nat → V → V → Nat) (leader : V → Bool)

/-- Physical construction cost in population, horizon, and binary labels.
The input is the actual shared DAG encoding, not an expanded history tree. -/
theorem anchorMatrix_physical_clean (t : Nat) (observer : V) (vista : Vista)
    (valid : vista.valid=true) (depth : (vista.node vista.bottom).level=t)
    (physical : decodeNode vista t vista.bottom=Counting.history G leader t observer)
    (anchor leaders M : Nat) (mass : ∀ r,0<r → r≤t → arcMass G r≤M) :
    let n:=Fintype.card V
    let K:=(t+1)*n
    let B:=t+K+M.size+n+1
    ∃ time output,
      time ≤ (20*(7000000053)^2)*(K*(8*B+9+n*(4*B+2))+2*anchor.size+2*leaders.size+5)^12 ∧
      HaltsAt anchorMatrixProgram (inputWord anchor leaders vista) time output ∧
      output.tape.denotes=Turing.Tape.mk₁ ((outputWord anchor leaders vista).map bitSymbol) := by
  dsimp only
  obtain ⟨time,output,bounded,halted,tape⟩ := anchorMatrix_clean anchor leaders vista
  have codeBound := Encoding.physical_vista_encoding_length G leader t observer vista valid depth physical M mass
  dsimp only at codeBound
  have inputBound : (inputWord anchor leaders vista).length+1 ≤
      (t+1)*Fintype.card V*(8*(t+(t+1)*Fintype.card V+M.size+Fintype.card V+1)+9+
        Fintype.card V*(4*(t+(t+1)*Fintype.card V+M.size+Fintype.card V+1)+2))+
          2*anchor.size+2*leaders.size+5 := by
    simp only [inputWord,List.length_append,Encoding.natural_length]
    omega
  exact ⟨time,output,bounded.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left inputBound 12)),halted,tape⟩

end Counting.Machine
