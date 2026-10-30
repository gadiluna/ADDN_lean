import Counting.CreditConsequences
import Counting.CoreCompleteness

/-! The mathematical shorter audit, whose candidate is `m` and whose
final visible level is `m-1`. Executable reconstruction is a separate layer. -/

namespace Counting.ShortAudit
open DirectedCounting PaperHistory

variable {V : Type*} [Fintype V]
variable (G : ℕ → V → V → ℕ) (leader : V → Bool)

/-- The soundness-relevant Steps 1--5 of the shorter audit. Anchor
flatness/unique solving are established separately for completeness. -/
structure Checks (m h : ℕ) (visible : ∀ r, Finset (Node G leader r))
    (candidate : ∀ r, Node G leader r → ℕ)
    extends CreditHistory.PrefixChecks G leader m h visible candidate where
  anchor_positive : 1 ≤ h
  anchor_le_final : h ≤ m - 1
  all_parent_visible : ∀ r, r < m - 1 → ∀ i ∈ visible (r + 1),
    parent G leader r i ∈ visible r
  all_children_nonempty : ∀ r, r < m - 1 → ∀ u ∈ visible r,
    ((visible (r + 1)).filter (fun i => parent G leader r i = u)).Nonempty
  suffix_nonflat : ∀ r, h ≤ r → r < m - 1 →
    ¬ ∀ u ∈ visible r, ((visible (r + 1)).filter (fun i => parent G leader r i = u)).card = 1
  suffix_audit : ∀ u ∈ visible h,
    ((visible (m - 1)).filter (fun i => CoreHistory.ancestor G leader h (m - 1) i = u)).card ≤
      candidate h u

namespace Checks
variable {G leader} {m h : ℕ} {visible : ∀ r, Finset (Node G leader r)}
  {candidate : ∀ r, Node G leader r → ℕ} (C : Checks G leader m h visible candidate)

noncomputable def potential (_C : Checks G leader m h visible candidate) (r : ℕ) : ℕ :=
  ∑ i ∈ visible r, credit (anonymity G leader r i) (candidate r i)

noncomputable def descendants (_C : Checks G leader m h visible candidate)
    (u : Node G leader h) : Finset (Node G leader (m - 1)) :=
  (visible (m - 1)).filter (fun i => CoreHistory.ancestor G leader h (m - 1) i = u)

include C

theorem suffix_growth : (visible h).card + (m - 1 - h) ≤ (visible (m - 1)).card := by
  have growth : ∀ k, h + k ≤ m - 1 → (visible h).card + k ≤ (visible (h + k)).card := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have hprior := ih (by omega)
      have hnext := CoreCertificate.card_lt_of_nonflat (parent G leader (h + k))
        (visible (h + k)) (visible (h + k + 1))
        (C.all_parent_visible (h + k) (by omega)) (C.all_children_nonempty (h + k) (by omega))
        (C.suffix_nonflat (h + k) (by omega) (by omega))
      have heq : h + (k + 1) = h + k + 1 := by omega
      rw [heq]
      omega
  have heq : h + (m - 1 - h) = m - 1 := Nat.add_sub_of_le C.anchor_le_final
  have result := growth (m - 1 - h) (by omega)
  rwa [heq] at result

theorem suffix_credit_bound : (visible (m - 1)).card ≤
    C.potential h + (visible h).card := by
  exact CoreCertificate.suffix_credit_bound (CoreHistory.ancestor G leader h (m - 1))
    (visible h) (visible (m - 1)) (anonymity G leader h) (candidate h)
    (anonymity G leader (m - 1))
    (CoreHistory.ancestor_visible_of_parent_visible G leader h (m - 1) C.anchor_le_final visible C.all_parent_visible)
    (CoreHistory.descendants_nonempty_of_children G leader h (m - 1) C.anchor_le_final visible C.all_children_nonempty)
    (fun i _ => anonymity_pos G leader (m - 1) i)
    (fun u _ => CoreHistory.descendants_mass_le G leader h (m - 1) C.anchor_le_final (visible (m - 1)) u)
    C.suffix_audit

theorem false_potential_bound (wrong : m ≠ Fintype.card V)
    (connected : ∀ t, 0 < t → StronglyConnected (fun u v => 0 < G t u v)) :
    C.potential h + h ≤ m - 1 := by
  have strict : ∀ r, r < h → C.potential (r + 1) < C.potential r := by
    intro r hr
    obtain ⟨hle, heq⟩ := C.toPrefixChecks.credit_loss r hr (connected (r + 1) (by omega))
    exact lt_of_le_of_ne hle (fun eq => wrong (heq eq).2.2)
  have drop : ∀ r, r ≤ h → C.potential r + r ≤ C.potential 0 := by
    intro r
    induction r with
    | zero => intro _; omega
    | succ r ih =>
      intro hr
      have hp := ih (by omega)
      have hs := strict r (by omega)
      omega
  exact (drop h le_rfl).trans C.toPrefixChecks.initial_credit_bound

/-- All inequalities in the paper's short-audit credit chain are tight. -/
theorem false_credit_tight (wrong : m ≠ Fintype.card V)
    (connected : ∀ t, 0 < t → StronglyConnected (fun u v => 0 < G t u v)) :
    C.potential h = m - 1 - h ∧
      (visible (m - 1)).card = C.potential h + (visible h).card := by
  have hupper := C.false_potential_bound wrong connected
  have hlower := C.suffix_credit_bound
  have hgrowth := C.suffix_growth
  have hanchor := C.anchor_le_final
  omega

theorem descendant_count_le_actual (u : Node G leader h) :
    (C.descendants u).card ≤ anonymity G leader h u :=
  CoreCompleteness.descendant_count_le_anonymity G leader h (m - 1) C.anchor_le_final _ u

/-- Tightness forces every anchor anonymity to equal its descendant count. -/
theorem false_anchor_actual_eq_descendants (wrong : m ≠ Fintype.card V)
    (connected : ∀ t, 0 < t → StronglyConnected (fun u v => 0 < G t u v)) :
    ∀ u ∈ visible h, anonymity G leader h u = (C.descendants u).card := by
  have maps := CoreHistory.ancestor_visible_of_parent_visible G leader h (m - 1)
    C.anchor_le_final visible C.all_parent_visible
  have hsum : (visible (m - 1)).card = ∑ u ∈ visible h, (C.descendants u).card :=
    Finset.card_eq_sum_card_fiberwise maps
  have bounds : ∀ u ∈ visible h,
      (C.descendants u).card ≤ credit (anonymity G leader h u) (candidate h u) + 1 := by
    intro u hu
    have ha := C.descendant_count_le_actual u
    have hb := C.suffix_audit u hu
    unfold credit
    change (C.descendants u).card ≤ candidate h u at hb
    omega
  have equalSum : (∑ u ∈ visible h, (C.descendants u).card) =
      ∑ u ∈ visible h, (credit (anonymity G leader h u) (candidate h u) + 1) := by
    rw [← hsum, (C.false_credit_tight wrong connected).2]
    simp only [potential, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
  have each := total_credit_eq_forces_local_eq (visible h)
    (fun u => credit (anonymity G leader h u) (candidate h u) + 1)
    (fun u => (C.descendants u).card) bounds equalSum
  intro u hu
  have heq := each u hu
  have ha := C.descendant_count_le_actual u
  have hb := C.suffix_audit u hu
  have hpos := anonymity_pos G leader h u
  change (C.descendants u).card ≤ candidate h u at hb
  unfold credit at heq
  omega

/-- Consequently every final visible fiber is a singleton. -/
theorem false_final_singleton (wrong : m ≠ Fintype.card V)
    (connected : ∀ t, 0 < t → StronglyConnected (fun u v => 0 < G t u v)) :
    ∀ i ∈ visible (m - 1), anonymity G leader (m - 1) i = 1 := by
  intro i hi
  let u := CoreHistory.ancestor G leader h (m - 1) i
  have hu := CoreHistory.ancestor_visible_of_parent_visible G leader h (m - 1)
    C.anchor_le_final visible C.all_parent_visible i hi
  have actual := C.false_anchor_actual_eq_descendants wrong connected u hu
  have hmass := CoreHistory.descendants_mass_le G leader h (m - 1) C.anchor_le_final (visible (m - 1)) u
  change (∑ j ∈ C.descendants u, anonymity G leader (m - 1) j) ≤ anonymity G leader h u at hmass
  rw [actual] at hmass
  have hsum : (∑ j ∈ C.descendants u, 1) =
      ∑ j ∈ C.descendants u, anonymity G leader (m - 1) j := by
    apply Nat.le_antisymm
    · exact Finset.sum_le_sum (fun j _ => anonymity_pos G leader (m - 1) j)
    · simpa using hmass
  exact (total_credit_eq_forces_local_eq (C.descendants u) (anonymity G leader (m - 1))
    (fun _ => 1) (fun j _ => anonymity_pos G leader (m - 1) j) hsum i
    (Finset.mem_filter.mpr ⟨hi, rfl⟩)).symm

end Checks
end Counting.ShortAudit
