import Counting.ExecutableRefinementComplete

namespace Counting.Executable
open Counting.TimingProtocolLocal
open scoped BigOperators

theorem certificate_backward_nodes (vista : Vista) (valid : vista.valid = true)
    (leaders candidate last r : Nat) (c : ∀ k, Counting.FullHistory k → Nat)
    (certificate : FullCertificate leaders candidate last r (decodedLevel vista) c)
    (k : Nat) (below : k < r + 1) (i : Nat) (present : i ∈ levelNodes vista k) :
    ((children vista i (k + 1)).map (fun j => c (k + 1) (decodeNode vista (k + 1) j))).sum =
      c k (decodeNode vista k i) := by
  classical
  have info := (mem_levelNodes vista k i).mp present
  have backward := certificate.backward k below (decodeNode vista k i)
    ((mem_decodedLevel vista k _).mpr ⟨i, info.1, info.2, rfl⟩)
  rw [sum_filter_decodedLevel vista valid, decoded_children_filter vista valid k i present] at backward
  exact backward

theorem fullCertificate_propagated (vista : Vista) (valid : vista.valid = true)
    (leaders candidate last r : Nat) (c : ∀ k, Counting.FullHistory k → Nat)
    (certificate : FullCertificate leaders candidate last r (decodedLevel vista) c)
    (k : Nat) (within : k ≤ r + 1) (i : Nat) (present : i ∈ levelNodes vista k) :
    (propagateWeights vista (r + 1) (anchorNatural vista r c))[i]?.getD 0 =
      c k (decodeNode vista k i) := by
  have helper : ∀ d k, k + d = r + 1 → ∀ i ∈ levelNodes vista k,
      (propagateWeights vista (r + 1) (anchorNatural vista r c))[i]?.getD 0 =
        c k (decodeNode vista k i) := by
    intro d
    induction d with
    | zero =>
        intro k equation i present
        have equal : k = r + 1 := by omega
        subst k
        obtain ⟨j, equal⟩ := List.mem_iff_get.mp present
        rw [← equal]
        change (propagateWeights vista (r + 1) (anchorNatural vista r c))[(levelNodes vista (r + 1))[j.val]]?.getD 0 = _
        rw [propagateWeights_anchor vista (r + 1) (anchorNatural vista r c) (anchorNatural_size vista r c) j,
          anchorNatural_coordinate]
        rfl
    | succ d ih =>
        intro k equation i present
        rw [propagateWeights_backward vista (r + 1) (anchorNatural vista r c) k (by omega) i present,
          ← certificate_backward_nodes vista valid leaders candidate last r c certificate k (by omega) i present]
        apply congrArg List.sum
        apply List.map_congr_left
        intro child hc
        exact ih (k + 1) (by omega) child (List.mem_filter.mp hc).1
  exact helper (r + 1 - k) k (by omega) i present

theorem fullCertificate_decoded_weights (vista : Vista) (valid : vista.valid = true)
    (leaders candidate last r : Nat) (c : ∀ k, Counting.FullHistory k → Nat)
    (certificate : FullCertificate leaders candidate last r (decodedLevel vista) c)
    (k : Nat) (within : k ≤ r + 1) (H : Counting.FullHistory k) (present : H ∈ decodedLevel vista k) :
    decodedWeight vista (propagateWeights vista (r + 1) (anchorNatural vista r c)) k H = c k H := by
  obtain ⟨i, hi, li, rfl⟩ := (mem_decodedLevel vista k H).mp present
  have stored := (mem_levelNodes vista k i).mpr ⟨hi, li⟩
  rw [decodedWeight_decode vista valid _ k i stored]
  exact fullCertificate_propagated vista valid leaders candidate last r c certificate k within i stored

theorem fullCertificate_flow_weights (vista : Vista) (valid : vista.valid = true)
    (leaders candidate last r : Nat) (c : ∀ k, Counting.FullHistory k → Nat)
    (certificate : FullCertificate leaders candidate last r (decodedLevel vista) c)
    (k : Nat) (below : k < r + 1) (old : Nat) (present : old ∈ levelNodes vista k) :
    ((levelNodes vista (k + 1)).map (fun i => countFrom (vista.node i) old *
      (propagateWeights vista (r + 1) (anchorNatural vista r c))[i]?.getD 0)).sum =
    ((children vista old (k + 1)).map (fun i => (vista.node i).degree *
      (propagateWeights vista (r + 1) (anchorNatural vista r c))[i]?.getD 0)).sum := by
  classical
  rw [← sum_decoded_red_weights vista valid _ k old present,
    ← sum_decoded_degree_weights vista valid _ k old present]
  have info := (mem_levelNodes vista k old).mp present
  have flow := certificate.candidate_flow k below (decodeNode vista k old)
    ((mem_decodedLevel vista k _).mpr ⟨old, info.1, info.2, rfl⟩)
  convert flow.symm using 1 <;>
    apply Finset.sum_congr rfl <;>
    intro H hH <;>
    rw [fullCertificate_decoded_weights vista valid leaders candidate last r c certificate (k + 1) (by omega) H hH]

theorem find_reverse_range_of_maximum (predicate : Nat → Bool) (bound anchor : Nat)
    (within : anchor < bound) (passes : predicate anchor = true)
    (maximal : ∀ k, anchor < k → k < bound → predicate k = false) :
    (List.range bound).reverse.find? predicate = some anchor := by
  induction bound with
  | zero => omega
  | succ bound ih =>
      rw [List.range_succ, List.reverse_append]
      simp only [List.reverse_singleton, List.singleton_append, List.find?_cons]
      by_cases equal : anchor = bound
      · subst anchor
        rw [passes]
      · have below : anchor < bound := by omega
        rw [maximal bound below (Nat.lt_succ_self bound)]
        exact ih below (fun k hk hb => maximal k hk (Nat.lt_succ_of_lt hb))

theorem fullCertificate_anchor_found (vista : Vista) (valid : vista.valid = true)
    (leaders candidate last r : Nat) (c : ∀ k, Counting.FullHistory k → Nat)
    (certificate : FullCertificate leaders candidate last r (decodedLevel vista) c)
    (within : last ≤ (vista.node vista.bottom).level) :
    (List.range (last + 1)).reverse.find? (flat vista) = some (r + 1) := by
  classical
  have anchorWithin := certificate.anchor_le_final
  apply find_reverse_range_of_maximum _ _ _ (by omega)
  · have nonempty := levelNodes_nonempty_of_le vista valid r (by omega)
    simp only [flat, Bool.and_eq_true, Nat.add_sub_cancel, decide_eq_true_eq]
    refine ⟨⟨by omega, ?_⟩, ?_⟩
    · cases h : levelNodes vista r with
      | nil => exact False.elim (nonempty h)
      | cons head rest => rfl
    · apply List.all_eq_true.mpr
      intro old present
      have info := (mem_levelNodes vista r old).mp present
      have flat := certificate.anchor_flat (decodeNode vista r old)
        ((mem_decodedLevel vista r _).mpr ⟨old, info.1, info.2, rfl⟩)
      rw [decoded_children_card vista valid r old present] at flat
      exact beq_iff_eq.mpr flat
  · intro k lower upper
    cases hk : flat vista k with
    | false => rfl
    | true =>
        exfalso
        have noFlat := certificate.suffix_nonflat (k - 1) (by omega) (by omega)
        apply noFlat
        intro H hH
        obtain ⟨i, hi, li, rfl⟩ := (mem_decodedLevel vista (k - 1) H).mp hH
        have present := (mem_levelNodes vista (k - 1) i).mpr ⟨hi, li⟩
        rw [decoded_children_card vista valid (k - 1) i present]
        have kk : k - 1 + 1 = k := by omega
        rw [kk]
        simp only [flat, Bool.and_eq_true] at hk
        exact beq_iff_eq.mp (List.all_eq_true.mp hk.2 i present)

end Counting.Executable
