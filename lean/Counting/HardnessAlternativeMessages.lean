import Counting.HardnessAlternativeGraph

namespace Counting.HardnessAlternative
open Counting.HardnessPath
open scoped Classical

variable {I : Type}

noncomputable def returnCount (zero i : I) (r n p : Nat) : Nat := by
  classical
  exact if i = zero ∧ p = r then 2 else
    if i ≠ zero ∧ p = r ∧ p+1 < n then 0 else 1

theorem edge_to_leader (coeff size : I → Nat) (zero : I) (r : Nat) (a : Member size) :
    edge coeff size zero r (some a) none = returnCount zero a.1 r (size a.1) a.2.val := by
  classical
  unfold edge destination copies returnCount
  split_ifs <;> simp_all
  omega

theorem returnCount_early (zero i : I) (r n p : Nat) (early : p < r) :
    returnCount zero i r n p = 1 := by
  simp [returnCount, Nat.ne_of_lt early]

theorem returnCount_after (zero i : I) (r n p : Nat) (after : r < p) :
    returnCount zero i r n p = 1 := by
  simp [returnCount, Nat.ne_of_gt after]

variable [Fintype I]

theorem group_receipts_short (coeff : I → Nat) (C r : Nat) (zero i : I) :
    (∑ p : Fin (r+1), Multiset.replicate (returnCount zero i r (r+1) p.val)
      (memberHistory coeff C r i p.val)) =
      (∑ p : Fin r, ({memberHistory coeff C r i p.val} : Multiset (FullHistory r))) +
        Multiset.replicate (if i = zero then 2 else 1) (memberHistory coeff C r i r) := by
  classical
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]
  have prefixSum : (∑ p : Fin r, Multiset.replicate (returnCount zero i r (r+1) p.val)
      (memberHistory coeff C r i p.val)) =
      ∑ p : Fin r, ({memberHistory coeff C r i p.val} : Multiset (FullHistory r)) := by
    apply Finset.sum_congr rfl
    intro p _
    rw [returnCount_early zero i r (r+1) p.val p.isLt, Multiset.replicate_one]
  rw [prefixSum]
  congr 2
  simp [returnCount]

theorem group_receipts_long (coeff : I → Nat) (C r : Nat) (zero i : I) (different : i ≠ zero) :
    (∑ p : Fin (r+2), Multiset.replicate (returnCount zero i r (r+2) p.val)
      (memberHistory coeff C r i p.val)) =
      (∑ p : Fin r, ({memberHistory coeff C r i p.val} : Multiset (FullHistory r))) +
        {memberHistory coeff C r i r} := by
  rw [show r+2 = (r+1)+1 from rfl, Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]
  have prefixSum : (∑ p : Fin r, Multiset.replicate (returnCount zero i r ((r+1)+1) p.val)
      (memberHistory coeff C r i p.val)) =
      ∑ p : Fin r, ({memberHistory coeff C r i p.val} : Multiset (FullHistory r)) := by
    apply Finset.sum_congr rfl
    intro p _
    rw [returnCount_early zero i r _ p.val p.isLt, Multiset.replicate_one]
  rw [prefixSum]
  have relay : returnCount zero i r ((r+1)+1) r = 0 := by simp [returnCount, different]
  rw [relay, Multiset.replicate_zero, add_zero,
    returnCount_after zero i r _ (r+1) (by omega), Multiset.replicate_one,
    member_suffix coeff C r i (r+1) (by omega)]

theorem canonical_leader_receipts (coeff size : I → Nat) (C r : Nat) (zero : I)
    (zeroSize : size zero = r+1)
    (otherSizes : ∀ i, i ≠ zero → size i = r+1 ∨ size i = r+2)
    (weighted : (∑ i, coeff i * size i) = C) (lengths : ∀ i, r < size i) :
    incoming (edge coeff size zero r) (history (pathNetwork coeff size) (leader size) r) none =
      ∑ i : I, ((∑ p : Fin r, ({memberHistory coeff C r i p.val} : Multiset (FullHistory r))) +
        Multiset.replicate (if i = zero then 2 else 1) (memberHistory coeff C r i r)) := by
  classical
  unfold incoming
  rw [Fintype.sum_option]
  change Multiset.replicate 0 _ + _ = _
  rw [Multiset.replicate_zero, zero_add, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  simp only [edge_to_leader, (path_histories coeff size C weighted r lengths).2]
  by_cases distinguished : i = zero
  · subst i
    rw [zeroSize]
    exact group_receipts_short coeff C r zero zero
  · rcases otherSizes i distinguished with short | long
    · rw [short]
      exact group_receipts_short coeff C r zero i
    · rw [long]
      simpa only [if_neg distinguished, Multiset.replicate_one] using
        group_receipts_long coeff C r zero i distinguished

end Counting.HardnessAlternative
