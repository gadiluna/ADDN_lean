import Counting.ExternalSAT
import Mathlib.Logic.Equiv.Fin.Rotate

namespace Counting.External

/-- In a variable gadget, each position either keeps its partner or takes
the next partner. Injectivity forces the Boolean choice around the cycle. -/
def cycleChoice {V : Type*} (rotate : Equiv.Perm V) (choice : V → Bool) (v : V) : V :=
  if choice v then v else rotate v

theorem cycleChoice_false_forward {V : Type*} (rotate : Equiv.Perm V) (choice : V → Bool)
    (injective : Function.Injective (cycleChoice rotate choice)) (v : V)
    (off : choice v = false) : choice (rotate v) = false := by
  cases h : choice (rotate v) with
  | false => rfl
  | true =>
      have same : cycleChoice rotate choice v = cycleChoice rotate choice (rotate v) := by
        simp [cycleChoice, off, h]
      have equal := injective same
      rw [← equal, off] at h
      contradiction

theorem cycleChoice_invariant {V : Type*} [Fintype V] [DecidableEq V]
    (rotate : Equiv.Perm V) (choice : V → Bool)
    (injective : Function.Injective (cycleChoice rotate choice)) (v : V) :
    choice (rotate v) = choice v := by
  let off : Finset V := Finset.univ.filter (fun v => choice v = false)
  have closed : off.image rotate ⊆ off := by
    intro w hw
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      cycleChoice_false_forward rotate choice injective u (Finset.mem_filter.mp hu).2⟩
  have invariant : off.image rotate = off := Finset.eq_of_subset_of_card_le closed (by
    rw [Finset.card_image_of_injective _ rotate.injective])
  cases hv : choice v with
  | false => exact cycleChoice_false_forward rotate choice injective v hv
  | true =>
      cases hn : choice (rotate v) with
      | true => rfl
      | false =>
          have member : rotate v ∈ off := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩
          rw [← invariant] at member
          obtain ⟨u, hu, equal⟩ := Finset.mem_image.mp member
          have same := rotate.injective equal
          subst u
          have no := (Finset.mem_filter.mp hu).2
          rw [hv] at no
          contradiction

theorem cycleChoice_constant (n : ℕ) (choice : Fin (n + 1) → Bool)
    (injective : Function.Injective (cycleChoice (finRotate (n + 1)) choice)) :
    ∀ i, choice i = choice 0 := by
  intro i
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih =>
      have step := cycleChoice_invariant (finRotate (n + 1)) choice injective i.castSucc
      have rotate : finRotate (n + 1) i.castSucc = i.succ := by
        rcases i with ⟨i, hi⟩
        exact finRotate_of_lt hi
      rw [rotate] at step
      exact step.trans ih

end Counting.External
