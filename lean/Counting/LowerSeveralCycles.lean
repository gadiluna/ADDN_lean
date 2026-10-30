import Counting.LowerSeveralBounds
import Mathlib.Logic.Equiv.Fin.Rotate

/-! Unit directed cycles used in both delay portions of the lower bound. -/

namespace Counting.LowerSeveralCycles
open DirectedCounting
open scoped BigOperators

/-- One directed arc to the cyclic successor. -/
def edge (n : Nat) (u v : Fin n) : Nat := if finRotate n u = v then 1 else 0

theorem degree (n : Nat) (u : Fin n) : (∑v, edge n u v) = 1 := by
  simp [edge]

theorem incoming_eq {A : Type} (n : Nat) (state : Fin n → A) (v : Fin n) :
    incoming (edge n) state v = {state ((finRotate n).symm v)} := by
  classical
  unfold incoming
  simp only [edge, Equiv.apply_eq_iff_eq_symm_apply]
  calc
    _ = ∑u : Fin n, if u = (finRotate n).symm v then ({state u} : Multiset A) else 0 := by
      apply Finset.sum_congr rfl
      intro u _
      split_ifs <;> simp
    _ = _ := by simp

theorem rotate_castSucc (n : Nat) (i : Fin n) :
    finRotate (n + 1) i.castSucc = i.succ := finRotate_of_lt i.isLt

theorem connected (n : Nat) : StronglyConnected (fun u v ↦ 0 < edge n u v) := by
  cases n with
  | zero => intro u; exact Fin.elim0 u
  | succ n =>
      have fromZero : ∀v : Fin (n + 1), Relation.ReflTransGen (fun u v ↦ 0 < edge (n + 1) u v) 0 v := by
        intro v
        induction v using Fin.induction with
        | zero => exact .refl
        | succ i ih => exact ih.tail (by simp [edge])
      have toZero : ∀v : Fin (n + 1), Relation.ReflTransGen (fun u v ↦ 0 < edge (n + 1) u v) v 0 := by
        intro v
        induction v using Fin.reverseInduction with
        | last => exact .single (by simp [edge])
        | cast i ih => exact ih.head (by simp [edge])
      exact fun u v ↦ (toZero u).trans (fromZero v)

theorem loopless (n : Nat) (atLeastTwo : 2 ≤ n) (u : Fin n) : edge n u u = 0 := by
  have hne : finRotate n u ≠ u := by
    cases n with
    | zero => omega
    | succ n =>
        by_cases hu : u.val < n
        · have heq := finRotate_of_lt hu
          intro hfix
          have hv := congrArg Fin.val (heq.symm.trans hfix)
          change u.val + 1 = u.val at hv
          omega
        · have hlast : u = Fin.last n := by apply Fin.ext; simp; omega
          rw [hlast, finRotate_last]
          intro hfix
          have hv := congrArg Fin.val hfix
          simp only [Fin.val_zero, Fin.val_last] at hv
          omega
  exact if_neg hne

theorem multiplicity (n : Nat) (u v : Fin n) : edge n u v ≤ 1 := by
  simp only [edge]
  split_ifs <;> omega

/-- Any increasing pair of consecutive indices is a cycle arc. -/
theorem rotate_of_next (n : Nat) (u v : Fin n) (consecutive : u.val + 1 = v.val) :
    finRotate n u = v := by
  cases n with
  | zero => exact Fin.elim0 u
  | succ n =>
      have hu : u.val < n := by omega
      have h := finRotate_of_lt hu
      exact h.trans (Fin.ext consecutive)

end Counting.LowerSeveralCycles
