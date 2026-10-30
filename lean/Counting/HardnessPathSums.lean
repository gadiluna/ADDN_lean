import Counting.HardnessPathPrefix
import Mathlib.Algebra.BigOperators.Fin

namespace Counting.HardnessPath

variable {I : Type} [Fintype I]

/-- The multiset of old states in a group: one copy of every exposed
singleton, and one binary-counted block for the undistinguished suffix. -/
theorem member_histories_sum_add (coeff : I → Nat) (C r d : Nat) (i : I) :
    (∑ p : Fin (r + d), ({memberHistory coeff C r i p.val} : Multiset (FullHistory r))) =
      (∑ p : Fin r, ({memberHistory coeff C r i p.val} : Multiset (FullHistory r))) +
        Multiset.replicate d (memberHistory coeff C r i r) := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [show r + (d + 1) = (r + d) + 1 from Nat.add_assoc _ _ _ |>.symm,
        Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [ih, member_suffix coeff C r i (r + d) (by omega), Multiset.replicate_add]
      simp only [Multiset.replicate_one, add_assoc]

theorem member_histories_sum (coeff : I → Nat) (C r n : Nat) (i : I) (length : r ≤ n) :
    (∑ p : Fin n, ({memberHistory coeff C r i p.val} : Multiset (FullHistory r))) =
      (∑ p : Fin r, ({memberHistory coeff C r i p.val} : Multiset (FullHistory r))) +
        Multiset.replicate (n-r) (memberHistory coeff C r i r) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le length
  simpa only [Nat.add_sub_cancel_left] using member_histories_sum_add coeff C r d i

/-- The actual receipts of the leader in an ordinary star after r path
rounds, expressed only using the common canonical histories and group sizes. -/
theorem star_canonical_receipts (coeff size : I → Nat) (C r : Nat)
    (weighted : (∑ i, coeff i * size i) = C) (lengths : ∀ i, r < size i) :
    incoming (star coeff size) (history (pathNetwork coeff size) (leader size) r) none =
      ∑ i : I, ((∑ p : Fin r, ({memberHistory coeff C r i p.val} : Multiset (FullHistory r))) +
        Multiset.replicate (size i-r) (memberHistory coeff C r i r)) := by
  rw [star_incoming_leader, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  simp only [(path_histories coeff size C weighted r lengths).2]
  exact member_histories_sum coeff C r (size i) i (lengths i).le

end Counting.HardnessPath
