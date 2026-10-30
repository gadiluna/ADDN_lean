import Counting.ExternalCellular
import Mathlib.Logic.Equiv.Fin.Rotate

namespace Counting.External.MachineBridge
open Machine Cellular

/-- Totalization used only in tableaux: an actual halt repeats its last
configuration; it never counts as an extra successful machine transition. -/
def stutter (program : Program) (config : Machine.Config program) : Machine.Config program :=
  (Machine.step program config).getD config

theorem tape_write_nth (tape : Turing.Tape Symbol) (symbol : Symbol) (i : Int) :
    (tape.write symbol).nth i = if i = 0 then symbol else tape.nth i := by
  cases i with
  | ofNat n => cases n <;> rfl
  | negSucc n => rfl

/-- A finite row contains exactly the relative tape cells around its head.
Only those addresses in the row are asserted; buffer bounds ensure that
all addresses read within the claimed time lie there. -/
structure Represents {program : Program} {width : Nat}
    (machine : Machine.Config program) (row : Cellular.Config program (Fin width)) : Prop where
  control : row.control = machine.control
  tape : ∀ place, row.tape place = machine.tape.denotes.nth ((place.val : Int) - row.position.val)

theorem Represents.head {program : Program} {width : Nat}
    {machine : Machine.Config program} {row : Cellular.Config program (Fin width)}
    (rep : Represents machine row) : row.tape row.position = machine.tape.head := by
  simpa only [sub_self, Turing.Tape.nth_zero, Machine.Tape.denotes] using rep.tape row.position

theorem rotate_right_nat {width : Nat} (place : Fin width) (inside : place.val+1 < width) :
    (finRotate width place).val = place.val+1 := by
  cases width with
  | zero => exact place.elim0
  | succ width =>
      apply coe_finRotate_of_ne_last
      intro equal
      have := congrArg Fin.val equal
      simp only [Fin.val_last] at this
      omega

theorem rotate_left_nat {width : Nat} (place : Fin width) (inside : 0 < place.val) :
    ((finRotate width).symm place).val = place.val-1 := by
  letI : NeZero width := NeZero.of_pos place.pos
  apply coe_finRotate_symm_of_ne_zero
  intro equal
  have := congrArg Fin.val equal
  simp only [Fin.val_zero] at this
  omega

theorem rotate_noFixed (width : Nat) (large : 2 ≤ width) (place : Fin width) :
    finRotate width place ≠ place := by
  cases width with
  | zero => omega
  | succ width =>
      intro equal
      have values := congrArg Fin.val equal
      rw [coe_finRotate] at values
      by_cases last : place = Fin.last width
      · rw [if_pos last] at values
        have lastVal := congrArg Fin.val last
        simp only [Fin.val_last] at lastVal
        omega
      · rw [if_neg last] at values
        omega

/-- One cellular step agrees with one zipper step (or genuine halted
stuttering), provided that moving either way cannot cross the row boundary. -/
theorem Represents.step {program : Program} {width : Nat}
    {machine : Machine.Config program} {row : Cellular.Config program (Fin width)}
    (rep : Represents machine row) (left : 0 < row.position.val)
    (right : row.position.val+1 < width) :
    Represents (stutter program machine) (row.step (finRotate width)) := by
  have read := rep.head
  have ctrl := rep.control
  cases instruction : program.code machine.control machine.tape.head with
  | none =>
      simpa only [stutter, Machine.step, instruction, Option.map_none, Option.getD_none,
        Cellular.Config.step, ctrl, read] using rep
  | some result =>
      rcases result with ⟨next, action⟩
      cases action with
      | write symbol =>
          simp only [stutter, Machine.step, instruction, Option.map_some, Option.getD_some,
            Cellular.Config.step, ctrl, read]
          refine ⟨rfl, ?_⟩
          intro place
          change Function.update row.tape row.position symbol place =
            (machine.tape.write symbol).denotes.nth ((place.val : Int) - row.position.val)
          rw [Machine.Tape.denotes_write, tape_write_nth]
          by_cases same : place = row.position
          · subst place
            simp
          · rw [Function.update_of_ne same, rep.tape]
            have different : (place.val : Int) - row.position.val ≠ 0 := by
              intro equal
              apply same
              apply Fin.ext
              omega
            rw [if_neg different]
      | move direction =>
          cases direction with
          | left =>
              simp only [stutter, Machine.step, instruction, Option.map_some, Option.getD_some,
                Cellular.Config.step, ctrl, read]
              refine ⟨rfl, ?_⟩
              intro place
              change row.tape place = (machine.tape.move .left).denotes.nth
                ((place.val : Int) - ((finRotate width).symm row.position).val)
              rw [Machine.Tape.denotes_move, Turing.Tape.move_left_nth, rep.tape]
              congr 1
              have value := rotate_left_nat row.position left
              omega
          | right =>
              simp only [stutter, Machine.step, instruction, Option.map_some, Option.getD_some,
                Cellular.Config.step, ctrl, read]
              refine ⟨rfl, ?_⟩
              intro place
              change row.tape place = (machine.tape.move .right).denotes.nth
                ((place.val : Int) - (finRotate width row.position).val)
              rw [Machine.Tape.denotes_move, Turing.Tape.move_right_nth, rep.tape]
              congr 1
              have value := rotate_right_nat row.position right
              omega

end Counting.External.MachineBridge
