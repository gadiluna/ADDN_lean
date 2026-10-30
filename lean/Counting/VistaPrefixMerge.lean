import Counting.VistaIsomorphism

/-! Every visible prefix is the union of the vistas rooted at its final
visible nodes. Nodes are canonical histories; union therefore identifies
exactly the isomorphic shared subhistories. -/

namespace Counting.VistaIsomorphism
open TimingProtocolLocal

/-- Merging the vistas of all visible nodes at level k reconstructs every
earlier level of the observer's vista. No realizability assumption is needed. -/
theorem prefix_merge (t : Nat) (H : FullHistory t) (k r : Nat)
    (earlier : r ≤ k) (within : k ≤ t) :
    levels t H r = (levels t H k).biUnion (fun h => levels k h r) := by
  classical
  induction t generalizing k r with
  | zero =>
    have hk : k = 0 := by omega
    subst k
    have hr : r = 0 := by omega
    subst r
    simp only [levels_top, Finset.singleton_biUnion]
  | succ t ih =>
    by_cases last : k = t + 1
    · subst k
      simp only [levels_top, Finset.singleton_biUnion]
    · have before : k ≤ t := by omega
      rw [levels_succ_of_le r t H (by omega), levels_succ_of_le k t H before,
        Finset.union_biUnion, Finset.biUnion_biUnion]
      rw [ih H.1 k r earlier before]
      congr 1
      apply Finset.biUnion_congr rfl
      intro h _
      exact ih h k r earlier before

end Counting.VistaIsomorphism
