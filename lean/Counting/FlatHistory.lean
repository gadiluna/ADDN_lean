import Counting.FlatLevel
import DirectedCountingFormalization.PaperHistory

/-!
# The flat-level lemma for concrete directed multigraph histories

The level is the full quotient level, so exhaustiveness is built into the
index type rather than supplied as a matrix assumption. Flatness is injectivity
of the (always surjective) parent map. The matrix, degree labels, leader
normalization, positive true solution, and connected support are all derived
from the concrete execution. The conclusion holds over both ℚ and ℝ.
-/

namespace Counting.FlatHistory

open DirectedCounting DirectedCounting.PaperHistory
open scoped BigOperators

variable {V : Type*} [Fintype V]
variable (G : Nat → V → V → Nat) (leader : V → Bool) (t : Nat)

/-- Full-level flatness: every old node has exactly one child. Surjectivity
of the parent map is already a theorem of the concrete history model. -/
def Flat : Prop := Function.Injective (parent G leader t)

theorem flat_iff_unique_child : Flat G leader t ↔
    ∀ p : Node G leader t, ∃! c : Node G leader (t + 1), parent G leader t c = p := by
  constructor
  · intro flat p
    obtain ⟨c, hc⟩ := forgetMultigraphHistoryClass_surjective G leader t p
    refine ⟨c, hc, ?_⟩
    intro d hd
    exact flat (hd.trans hc.symm)
  · intro unique i j hij
    obtain ⟨c, _, huniq⟩ := unique (parent G leader t i)
    exact (huniq i rfl).trans (huniq j hij.symm).symm

noncomputable def weight (i j : Node G leader (t + 1)) : Nat :=
  redMultiplicity G leader t (parent G leader t i) j

noncomputable def leaders : Finset (Node G leader (t + 1)) :=
  Finset.univ.filter (fun c ↦ label G leader (t + 1) c = true)

noncomputable def leaderCount : Nat := by
  classical
  exact (Finset.univ.filter (fun v ↦ leader v = true)).card

/-- Physical arcs induce positive entries in the concrete quotient matrix. -/
theorem positive_weight_of_arc {u v : V} (hedge : 0 < G (t + 1) u v) :
    0 < weight G leader t (classOf G leader (t + 1) u)
      (classOf G leader (t + 1) v) := by
  classical
  unfold weight
  rw [parent_classOf]
  have hu : u ∈ fiber G leader t (classOf G leader t u) := by simp
  have hv : v ∈ fiber G leader (t + 1) (classOf G leader (t + 1) v) := by simp
  rw [← incoming_eq_redMultiplicity G leader t _ _ hv]
  unfold weightedIncomingCount
  exact lt_of_lt_of_le hedge
    (Finset.single_le_sum (f := fun u ↦ G (t + 1) u v) (fun _ _ ↦ Nat.zero_le _) hu)

/-- Contraction of the actual round graph yields connected positive support.
No assumption about the quotient graph is left to the caller. -/
theorem weight_stronglyConnected
    (hsc : StronglyConnected (fun u v ↦ 0 < G (t + 1) u v)) :
    StronglyConnected (fun i j ↦ 0 < weight G leader t i j) := by
  intro i j
  have path := hsc i.out j.out
  have mapped : Relation.ReflTransGen (fun i j ↦ 0 < weight G leader t i j)
      (classOf G leader (t + 1) i.out) (classOf G leader (t + 1) j.out) := by
    exact Relation.ReflTransGen.lift (classOf G leader (t + 1))
      (fun _ _ hedge ↦ positive_weight_of_arc G leader t hedge) _ _ path
  simpa using mapped

/-- For a flat full level, the old fiber's flow has only one child term. -/
theorem natural_flow (flat : Flat G leader t) (i : Node G leader (t + 1)) :
    (∑ j, weight G leader t i j * anonymity G leader (t + 1) j) =
      outdegreeLabel G leader t i * anonymity G leader (t + 1) i := by
  classical
  have hchildren : Finset.univ.filter
      (fun c : Node G leader (t + 1) ↦ parent G leader t c = parent G leader t i) = {i} := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact flat.eq_iff
  have h := flow_balance G leader t (parent G leader t i)
  simpa [weight, hchildren] using h

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- Actual anonymities solve the concrete flow equations in the chosen field. -/
theorem cast_flow (flat : Flat G leader t) :
    FlatLevel.Flow (fun i j ↦ (weight G leader t i j : K))
      (fun i ↦ (outdegreeLabel G leader t i : K))
      (fun i ↦ (anonymity G leader (t + 1) i : K)) := by
  intro i
  simpa only [Nat.cast_sum, Nat.cast_mul] using
    congrArg (fun n : Nat ↦ (n : K)) (natural_flow G leader t flat i)

/-- Abstract proportionality is instantiated on the actual history quotient. -/
theorem solutions_proportional [Nonempty V]
    (flat : Flat G leader t)
    (hsc : StronglyConnected (fun u v ↦ 0 < G (t + 1) u v))
    (z : Node G leader (t + 1) → K)
    (hz : FlatLevel.Flow (fun i j ↦ (weight G leader t i j : K))
      (fun i ↦ (outdegreeLabel G leader t i : K)) z) :
    ∃ c : K, ∀ i, z i = c * (anonymity G leader (t + 1) i : K) := by
  letI : Nonempty (Node G leader (t + 1)) :=
    ⟨classOf G leader (t + 1) (Classical.choice inferInstance)⟩
  have hconnected : ∀ i j, Relation.ReflTransGen
      (fun p q ↦ 0 < (weight G leader t p q : K)) i j := by
    intro i j
    have path := weight_stronglyConnected G leader t hsc i j
    induction path with
    | refl => exact .refl
    | tail _ hedge ih => exact ih.tail (by exact_mod_cast hedge)
  apply FlatLevel.flow_solution_proportional
      (fun i j ↦ (weight G leader t i j : K))
      (fun i ↦ (outdegreeLabel G leader t i : K))
      (fun i ↦ (anonymity G leader (t + 1) i : K)) z
  · intro i j; exact Nat.cast_nonneg _
  · intro i; exact_mod_cast anonymity_pos G leader (t + 1) i
  · exact hconnected
  · exact cast_flow G leader t flat
  · exact hz

/-- The manuscript's flat-level uniqueness lemma for a concrete execution.
There may be any positive number of leaders. The competing vector may have
arbitrary field values: positivity and integrality of the candidate are not
extra assumptions of uniqueness. -/
theorem flat_level_anonymities_unique [Nonempty V]
    (flat : Flat G leader t)
    (hsc : StronglyConnected (fun u v ↦ 0 < G (t + 1) u v))
    (hleaders : 0 < leaderCount leader)
    (z : Node G leader (t + 1) → K)
    (hz : FlatLevel.Flow (fun i j ↦ (weight G leader t i j : K))
      (fun i ↦ (outdegreeLabel G leader t i : K)) z)
    (hzleaders : ∑ i ∈ leaders G leader t, z i = (leaderCount leader : K)) :
    z = (fun i ↦ (anonymity G leader (t + 1) i : K)) := by
  obtain ⟨c, hc⟩ := solutions_proportional G leader t flat hsc z hz
  have hactual : (∑ i ∈ leaders G leader t,
      (anonymity G leader (t + 1) i : K)) = (leaderCount leader : K) := by
    exact_mod_cast label_mass_eq G leader (t + 1) true
  have hcount : (leaderCount leader : K) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hleaders)
  have hmul : c * (leaderCount leader : K) = (leaderCount leader : K) := by
    calc
      c * (leaderCount leader : K) =
          c * ∑ i ∈ leaders G leader t, (anonymity G leader (t + 1) i : K) := by
        rw [hactual]
      _ = ∑ i ∈ leaders G leader t, z i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ ↦ (hc i).symm)
      _ = (leaderCount leader : K) := hzleaders
  have hc1 : c = 1 := (mul_right_cancel₀ hcount) (by simpa using hmul)
  funext i
  simpa [hc1] using hc i

/-- Existence and uniqueness of the normalized full-level flow solution. -/
theorem flat_level_unique_solution [Nonempty V]
    (flat : Flat G leader t)
    (hsc : StronglyConnected (fun u v ↦ 0 < G (t + 1) u v))
    (hleaders : 0 < leaderCount leader) :
    ∃! z : Node G leader (t + 1) → K,
      FlatLevel.Flow (fun i j ↦ (weight G leader t i j : K))
        (fun i ↦ (outdegreeLabel G leader t i : K)) z ∧
      (∑ i ∈ leaders G leader t, z i) = (leaderCount leader : K) := by
  refine ⟨(fun i ↦ (anonymity G leader (t + 1) i : K)), ⟨cast_flow G leader t flat, ?_⟩, ?_⟩
  · simpa only [leaders, leaderCount, Nat.cast_sum] using
      congrArg (fun n : Nat ↦ (n : K)) (label_mass_eq G leader (t + 1) true)
  · intro z hz
    exact flat_level_anonymities_unique G leader t flat hsc hleaders z hz.1 hz.2

end Counting.FlatHistory
