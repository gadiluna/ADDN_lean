import Counting.ExternalMachineRun

namespace Counting.External.MachineBridge
open Machine Cellular

/-- Common finite width for all inputs up to the chosen capacity. The
extra cells put both wrap boundaries beyond the time-limited head range. -/
def width (capacity time : Nat) : Nat := capacity+2*time+3

def initialConfig (program : Program) (input : List Bool) (capacity time : Nat) :
    Cellular.Config program (Fin (width capacity time)) where
  control := 0
  position := ⟨time+1, by unfold width; omega⟩
  tape place := (Machine.initial program input).tape.denotes.nth ((place.val : Int) - (time+1 : Nat))

theorem initial_represents (program : Program) (input : List Bool) (capacity time : Nat) :
    Represents (Machine.initial program input) (initialConfig program input capacity time) := ⟨rfl, fun _ => rfl⟩

/-- Finite synchronous run with halted configurations held constant. -/
def rowRun (program : Program) (input : List Bool) (capacity time : Nat) :
    Nat → Cellular.Config program (Fin (width capacity time))
  | 0 => initialConfig program input capacity time
  | round+1 => (rowRun program input capacity time round).step (finRotate (width capacity time))

theorem position_step_bounds {program : Program} {w : Nat}
    (row : Cellular.Config program (Fin w)) (left : 0 < row.position.val)
    (right : row.position.val+1 < w) :
    row.position.val ≤ (row.step (finRotate w)).position.val+1 ∧
      (row.step (finRotate w)).position.val ≤ row.position.val+1 := by
  cases instruction : program.code row.control (row.tape row.position) with
  | none => simp only [Cellular.Config.step, instruction]; omega
  | some result =>
      rcases result with ⟨next, action⟩
      cases action with
      | write symbol => simp only [Cellular.Config.step, instruction]; omega
      | move direction =>
          cases direction with
          | left =>
              simp only [Cellular.Config.step, instruction]
              rw [rotate_left_nat _ left]
              omega
          | right =>
              simp only [Cellular.Config.step, instruction]
              rw [rotate_right_nat _ right]
              omega

/-- At most one head move per true transition. The head never approaches
either wrap boundary during the first `time` rows. -/
theorem rowRun_buffer (program : Program) (input : List Bool) (capacity time round : Nat)
    (bounded : round ≤ time) :
    time+1 ≤ (rowRun program input capacity time round).position.val+round ∧
      (rowRun program input capacity time round).position.val ≤ time+1+round := by
  induction round with
  | zero => simp only [rowRun, initialConfig, Nat.add_zero]; exact ⟨le_rfl, le_rfl⟩
  | succ round ih =>
      obtain ⟨lower, upper⟩ := ih (by omega)
      have left : 0 < (rowRun program input capacity time round).position.val := by omega
      have right : (rowRun program input capacity time round).position.val+1 < width capacity time := by
        unfold width
        omega
      obtain ⟨decrease, increase⟩ := position_step_bounds (rowRun program input capacity time round) left right
      change time+1 ≤ ((rowRun program input capacity time round).step (finRotate (width capacity time))).position.val+(round+1) ∧
        ((rowRun program input capacity time round).step (finRotate (width capacity time))).position.val ≤ time+1+(round+1)
      omega

theorem rowRun_interior (program : Program) (input : List Bool) (capacity time round : Nat)
    (bounded : round ≤ time) :
    0 < (rowRun program input capacity time round).position.val ∧
      (rowRun program input capacity time round).position.val+1 < width capacity time := by
  obtain ⟨lower, upper⟩ := rowRun_buffer program input capacity time round bounded
  unfold width
  omega

/-- Exact simulation, including all tape cells in the finite row and the
control state. The buffer is derived from time; it is not a premise about
an unknown computation. -/
theorem rowRun_represents (program : Program) (input : List Bool) (capacity time round : Nat)
    (bounded : round ≤ time) :
    Represents (stutterRun program round (Machine.initial program input))
      (rowRun program input capacity time round) := by
  induction round with
  | zero => exact initial_represents program input capacity time
  | succ round ih =>
      have previous := ih (by omega)
      have interior := rowRun_interior program input capacity time round (by omega)
      exact previous.step interior.1 interior.2

/-- The unique-head configuration and the radius-one finite-cell dynamics
produce the same complete rows. -/
theorem rowRun_encoded (program : Program) (input : List Bool) (capacity time round : Nat) :
    (rowRun program input capacity time round).encoded =
      (Cellular.dynamics program (finRotate (width capacity time))).run round
        (initialConfig program input capacity time).encoded := by
  induction round with
  | zero => rfl
  | succ round ih =>
      change ((rowRun program input capacity time round).step (finRotate (width capacity time))).encoded = _
      rw [Cellular.encoded_step program _ (rotate_noFixed _ (by unfold width; omega)), ih]
      rfl

/-- Accepting at the padded final row is exactly real halted acceptance
within the stated number of primitive Turing transitions. -/
theorem bounded_accepts_iff (program : Program) (input : List Bool) (capacity time : Nat) :
    (∃ place, Cellular.accept program
      ((Cellular.dynamics program (finRotate (width capacity time))).run time
        (initialConfig program input capacity time).encoded place) = true) ↔
      ∃ steps ≤ time, ∃ output,
        Machine.HaltsAt program input steps output ∧ program.accept output.control = true := by
  rw [← rowRun_encoded, Cellular.exists_accept_encoded]
  have rep := rowRun_represents program input capacity time time le_rfl
  rw [rep.control, rep.head]
  rw [← stutterRun_accepts_iff]
  simp only [Machine.step, Option.map_eq_none_iff]

end Counting.External.MachineBridge
