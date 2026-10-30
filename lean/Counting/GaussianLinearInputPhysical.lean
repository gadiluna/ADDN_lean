import Counting.GaussianLinearInputSize
import Counting.LabelBounds

namespace Counting.GaussianLinearInputSize
open Executable GaussianNormalMatrix

variable {V : Type} [Fintype V]
variable (G : Nat  →  V  →  V  →  Nat) (leader : V  →  Bool)

/-- The actual integral solver input for an anchor of a physical view has
polynomial length in the population and the binary labels. This statement
bounds serialization length, without charging the construction of the
anchor equations to the solver itself. -/
theorem physical_anchor_input_length (t : Nat) (observer : V) (vista : Vista)
    (valid : vista.valid=true) (depth : (vista.node vista.bottom).level=t)
    (physical : decodeNode vista t vista.bottom=Counting.history G leader t observer)
    (anchor leaders M : Nat)
    (mass : ∀ r,0 < r → r ≤ t → arcMass G r ≤ M) :
    (StackMachine.GaussianNormal.inputWord (levelNodes vista anchor).length
      (equationMatrix (levelNodes vista anchor).length (anchorRows vista anchor leaders))).length ≤ 
      100*(Fintype.card V+1)^2*(M.size+leaders.size+3) := by
  have sized := anchor_input_length vista anchor leaders M
    (fun i inside => (stored_labels_le G leader t observer vista valid depth physical M mass i inside).1)
    (fun i inside old => countFrom_le_arc_bound G leader t observer vista valid depth physical M mass i old inside)
  have width := levelNodes_length_le_card G leader t observer vista valid depth physical anchor
  have count := levelNodes_length_le_card G leader t observer vista valid depth physical (anchor-1)
  have polynomial := inputBound_polynomial (levelNodes vista anchor).length ((levelNodes vista (anchor-1)).length+1) (M.size+leaders.size+2) (Fintype.card V) width (by omega)
  exact sized.trans polynomial

end Counting.GaussianLinearInputSize
