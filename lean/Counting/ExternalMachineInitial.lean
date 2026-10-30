import Counting.ExternalMachineSimulation
import Counting.ExternalWitnessWord

namespace Counting.External.MachineBridge
open Machine Cellular

theorem ofWord_nth_nat (symbols : List Symbol) (position : Nat) :
    (Machine.Tape.ofWord symbols).denotes.nth (position : Int) = (symbols[position]?).getD .blank := by
  rw [Machine.Tape.denotes_ofWord]
  change (Turing.Tape.mk' (Turing.ListBlank.mk []) (Turing.ListBlank.mk symbols)).nth (position : Int) = _
  rw [Turing.Tape.mk'_nth_nat, Turing.ListBlank.nth_mk,
    ← List.getD_default_eq_getI, List.getD_eq_getElem?_getD]
  rfl

theorem ofWord_nth_negative (symbols : List Symbol) (position : Int) (negative : position < 0) :
    (Machine.Tape.ofWord symbols).denotes.nth position = .blank := by
  cases position with
  | ofNat position => exact False.elim ((Int.natCast_nonneg position).not_gt negative)
  | negSucc position =>
      change (Turing.ListBlank.mk ([] : List Symbol)).nth position = .blank
      simp [Turing.ListBlank.nth_mk]
      rfl

/-- Concrete initial row symbols are the listed input bits after the head
position and blank everywhere to its left. -/
theorem initial_tape (program : Program) (input : List Bool) (capacity time : Nat)
    (place : Fin (width capacity time)) :
    (initialConfig program input capacity time).tape place =
      if place.val < time+1 then .blank else WitnessWord.read input (place.val-(time+1)) := by
  change (Machine.Tape.ofWord (input.map bitSymbol)).denotes.nth
    ((place.val : Int)-(time+1 : Nat)) = _
  by_cases before : place.val < time+1
  · rw [if_pos before]
    exact ofWord_nth_negative _ _ (by omega)
  · rw [if_neg before]
    have difference : (place.val : Int)-(time+1 : Nat) = (place.val-(time+1) : Nat) := by omega
    rw [difference, ofWord_nth_nat]
    rfl

end Counting.External.MachineBridge
