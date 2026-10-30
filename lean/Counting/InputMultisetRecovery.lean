import Counting.FlatLevel
import Counting.CoreCertificate
import DirectedCountingFormalization.PaperHistory
import Mathlib.Data.Multiset.Fintype

/-! Exact reconstruction of input multiplicities from complete flat levels,
normalized by the known population, for arbitrary input labels. -/

namespace Counting.InputMultisetRecovery

open DirectedCounting DirectedCounting.PaperHistory
open scoped BigOperators

variable {V Input : Type*} [Fintype V]
variable (G : Nat → V → V → Nat) (input : V → Input) (t : Nat)

/-- Full-level flatness: every old node has exactly one child. Surjectivity
of the parent map is already a theorem of the concrete history model. -/
def Flat : Prop := Function.Injective (parent G input t)

theorem flat_iff_unique_child : Flat G input t ↔
    ∀ p : Node G input t, ∃! c : Node G input (t + 1), parent G input t c = p := by
  constructor
  · intro flat p
    obtain ⟨c, hc⟩ := forgetMultigraphHistoryClass_surjective G input t p
    refine ⟨c, hc, ?_⟩
    intro d hd
    exact flat (hd.trans hc.symm)
  · intro unique i j hij
    obtain ⟨c, _, huniq⟩ := unique (parent G input t i)
    exact (huniq i rfl).trans (huniq j hij.symm).symm

noncomputable def weight (i j : Node G input (t + 1)) : Nat :=
  redMultiplicity G input t (parent G input t i) j

/-- Physical arcs induce positive entries in the concrete quotient matrix. -/
theorem positive_weight_of_arc {u v : V} (hedge : 0 < G (t + 1) u v) :
    0 < weight G input t (classOf G input (t + 1) u)
      (classOf G input (t + 1) v) := by
  classical
  unfold weight
  rw [parent_classOf]
  have hu : u ∈ fiber G input t (classOf G input t u) := by simp
  have hv : v ∈ fiber G input (t + 1) (classOf G input (t + 1) v) := by simp
  rw [← incoming_eq_redMultiplicity G input t _ _ hv]
  unfold weightedIncomingCount
  exact lt_of_lt_of_le hedge
    (Finset.single_le_sum (f := fun u ↦ G (t + 1) u v) (fun _ _ ↦ Nat.zero_le _) hu)

/-- Contraction of the actual round graph yields connected positive support.
No assumption about the quotient graph is left to the caller. -/
theorem weight_stronglyConnected
    (hsc : StronglyConnected (fun u v ↦ 0 < G (t + 1) u v)) :
    StronglyConnected (fun i j ↦ 0 < weight G input t i j) := by
  intro i j
  have path := hsc i.out j.out
  have mapped : Relation.ReflTransGen (fun i j ↦ 0 < weight G input t i j)
      (classOf G input (t + 1) i.out) (classOf G input (t + 1) j.out) := by
    exact Relation.ReflTransGen.lift (classOf G input (t + 1))
      (fun _ _ hedge ↦ positive_weight_of_arc G input t hedge) _ _ path
  simpa using mapped

/-- For a flat full level, the old fiber's flow has only one child term. -/
theorem natural_flow (flat : Flat G input t) (i : Node G input (t + 1)) :
    (∑ j, weight G input t i j * anonymity G input (t + 1) j) =
      outdegreeLabel G input t i * anonymity G input (t + 1) i := by
  classical
  have hchildren : Finset.univ.filter
      (fun c : Node G input (t + 1) ↦ parent G input t c = parent G input t i) = {i} := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact flat.eq_iff
  have h := flow_balance G input t (parent G input t i)
  simpa [weight, hchildren] using h

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- Actual anonymities solve the concrete flow equations in the chosen field. -/
theorem cast_flow (flat : Flat G input t) :
    FlatLevel.Flow (fun i j ↦ (weight G input t i j : K))
      (fun i ↦ (outdegreeLabel G input t i : K))
      (fun i ↦ (anonymity G input (t + 1) i : K)) := by
  intro i
  simpa only [Nat.cast_sum, Nat.cast_mul] using
    congrArg (fun n : Nat ↦ (n : K)) (natural_flow G input t flat i)

/-- Abstract proportionality is instantiated on the actual history quotient. -/
theorem solutions_proportional [Nonempty V]
    (flat : Flat G input t)
    (hsc : StronglyConnected (fun u v ↦ 0 < G (t + 1) u v))
    (z : Node G input (t + 1) → K)
    (hz : FlatLevel.Flow (fun i j ↦ (weight G input t i j : K))
      (fun i ↦ (outdegreeLabel G input t i : K)) z) :
    ∃ c : K, ∀ i, z i = c * (anonymity G input (t + 1) i : K) := by
  letI : Nonempty (Node G input (t + 1)) :=
    ⟨classOf G input (t + 1) (Classical.choice inferInstance)⟩
  have hconnected : ∀ i j, Relation.ReflTransGen
      (fun p q ↦ 0 < (weight G input t p q : K)) i j := by
    intro i j
    have path := weight_stronglyConnected G input t hsc i j
    induction path with
    | refl => exact .refl
    | tail _ hedge ih => exact ih.tail (by exact_mod_cast hedge)
  apply FlatLevel.flow_solution_proportional
      (fun i j ↦ (weight G input t i j : K))
      (fun i ↦ (outdegreeLabel G input t i : K))
      (fun i ↦ (anonymity G input (t + 1) i : K)) z
  · intro i j; exact Nat.cast_nonneg _
  · intro i; exact_mod_cast anonymity_pos G input (t + 1) i
  · exact hconnected
  · exact cast_flow G input t flat
  · exact hz

/-- Known population fixes the scalar of the flat flow solution. -/
theorem normalized_flow_unique [Nonempty V]
    (flat : Flat G input t)
    (hsc : StronglyConnected (fun u v => 0 < G (t + 1) u v))
    (z : Node G input (t + 1) → K)
    (hz : FlatLevel.Flow (fun i j => (weight G input t i j : K))
      (fun i => (outdegreeLabel G input t i : K)) z)
    (htotal : ∑ i, z i = (Fintype.card V : K)) :
    z = (fun i => (anonymity G input (t + 1) i : K)) := by
  obtain ⟨c, hc⟩ := solutions_proportional G input t flat hsc z hz
  have hactual : (∑ i : Node G input (t + 1),
      (anonymity G input (t + 1) i : K)) = (Fintype.card V : K) := by
    exact_mod_cast total_anonymity G input (t + 1)
  have hcount : (Fintype.card V : K) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hmul : c * (Fintype.card V : K) = (Fintype.card V : K) := by
    calc
      c * (Fintype.card V : K) = c * ∑ i : Node G input (t + 1),
          (anonymity G input (t + 1) i : K) := by rw [hactual]
      _ = ∑ i : Node G input (t + 1), z i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => (hc i).symm)
      _ = (Fintype.card V : K) := htotal
  have hc1 : c = 1 := (mul_right_cancel₀ hcount) (by simpa using hmul)
  funext i
  simpa [hc1] using hc i

/-- Existence and uniqueness of the population-normalized rational system. -/
theorem normalized_flow_existsUnique [Nonempty V]
    (flat : Flat G input t)
    (hsc : StronglyConnected (fun u v => 0 < G (t + 1) u v)) :
    ∃! z : Node G input (t + 1) → ℚ,
      FlatLevel.Flow (fun i j => (weight G input t i j : ℚ))
        (fun i => (outdegreeLabel G input t i : ℚ)) z ∧
      (∑ i, z i) = (Fintype.card V : ℚ) := by
  refine ⟨fun i => (anonymity G input (t + 1) i : ℚ), ⟨cast_flow G input t flat, ?_⟩, ?_⟩
  · change (∑ i : Node G input (t + 1), (anonymity G input (t + 1) i : ℚ)) = _
    exact_mod_cast total_anonymity G input (t + 1)
  · intro z hz
    exact normalized_flow_unique G input t flat hsc z hz.1 hz.2

/-- Nonflat transitions strictly increase the number of input histories. -/
theorem card_strict_of_nonflat (nonflat : ¬ Flat G input t) :
    Fintype.card (Node G input t) < Fintype.card (Node G input (t + 1)) := by
  classical
  have h := CoreCertificate.card_lt_of_nonflat (parent G input t) Finset.univ Finset.univ
    (fun i _ => Finset.mem_univ _) ?_ ?_
  · simpa using h
  · intro u _
    obtain ⟨i, hi⟩ := forgetMultigraphHistoryClass_surjective G input t u
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  · intro hflat
    apply nonflat
    apply (flat_iff_unique_child G input t).mpr
    intro u
    exact (Fintype.existsUnique_iff_card_one _).mpr (hflat u (Finset.mem_univ u))

/-- Two distinct inputs force a complete flat transition by level `n - 1`. -/
theorem exists_early_flat_of_nonconstant
    (different : ∃ u v, input u ≠ input v) :
    ∃ r, r + 1 ≤ Fintype.card V - 1 ∧ Flat G input r := by
  classical
  obtain ⟨u, v, huv⟩ := different
  have hnodes : classOf G input 0 u ≠ classOf G input 0 v := by
    intro heq
    exact huv ((classOf_eq_iff G input 0 u v).mp heq)
  have hzero : 2 ≤ Fintype.card (Node G input 0) := by
    exact Fintype.one_lt_card_iff.mpr ⟨_, _, hnodes⟩
  have upper : ∀ r, Fintype.card (Node G input r) ≤ Fintype.card V := by
    intro r
    exact Fintype.card_le_of_surjective (classOf G input r)
      (fun c => ⟨c.out, classOf_out G input r c⟩)
  have hn : 2 ≤ Fintype.card V := le_trans hzero (upper 0)
  by_contra h
  push Not at h
  have growth : ∀ r, r ≤ Fintype.card V - 1 →
      Fintype.card (Node G input 0) + r ≤ Fintype.card (Node G input r) := by
    intro r
    induction r with
    | zero => intro _; omega
    | succ r ih =>
      intro hr
      have hp := ih (by omega)
      have hs := card_strict_of_nonflat G input r (h r hr)
      omega
  have lower := growth (Fintype.card V - 1) le_rfl
  have limit := upper (Fintype.card V - 1)
  omega

/-- The answer does not depend on any ordering of agents. -/
noncomputable def populationMultiset : Multiset Input :=
  (Finset.univ : Finset V).val.map input

/-- Recombine history classes using candidate multiplicities. -/
noncomputable def weightedMultiset (counts : Node G input t → ℕ) : Multiset Input :=
  ∑ c, Multiset.replicate (counts c) (label G input t c)

/-- Exact class anonymities reconstruct precisely the input multiset. -/
theorem weighted_multiset_eq :
    weightedMultiset G input t (anonymity G input t) = populationMultiset input := by
  classical
  apply Multiset.ext.mpr
  intro a
  have sum_count : ∀ (s : Finset (Node G input t)),
      (∑ c ∈ s, Multiset.replicate (anonymity G input t c)
        (label G input t c)).count a =
      ∑ c ∈ s, if label G input t c = a then anonymity G input t c else 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert c s hc ih =>
      simp [Finset.sum_insert, hc, Multiset.count_replicate, ih, eq_comm]
  rw [weightedMultiset, sum_count]
  have hm := label_mass_eq G input t a
  rw [Finset.sum_filter] at hm
  rw [hm]
  simp [populationMultiset, Multiset.count_map, ← Finset.filter_val, eq_comm]

/-- Constant inputs need no flow system once the population is known. -/
theorem populationMultiset_constant (a : Input) (constant : ∀ v, input v = a) :
    populationMultiset input = Multiset.replicate (Fintype.card V) a := by
  classical
  simp [populationMultiset, show input = fun _ => a from funext constant]

/-- Integral solutions of the normalized system return exactly the input multiset. -/
theorem normalized_natural_multiset_eq [Nonempty V]
    (flat : Flat G input t)
    (hsc : StronglyConnected (fun u v => 0 < G (t + 1) u v))
    (counts : Node G input (t + 1) → ℕ)
    (flow : FlatLevel.Flow (fun i j => (weight G input t i j : ℚ))
      (fun i => (outdegreeLabel G input t i : ℚ)) (fun i => (counts i : ℚ)))
    (total : ∑ i, counts i = Fintype.card V) :
    weightedMultiset G input (t + 1) counts = populationMultiset input := by
  have heq := normalized_flow_unique G input t flat hsc (fun i => (counts i : ℚ))
    flow (by exact_mod_cast total)
  have counts_eq : counts = anonymity G input (t + 1) := by
    funext i
    exact_mod_cast congrFun heq i
  rw [counts_eq]
  exact weighted_multiset_eq G input (t + 1)

end Counting.InputMultisetRecovery

