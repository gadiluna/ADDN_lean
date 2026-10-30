import Counting.Vista
import Counting.CoreHistory

/-!
# Parent closure and exhaustive prefixes of actual vistas

These lemmas concern the concrete observer's visibleNodes, not arbitrary
selected levels. No visible-child property is assumed for an arbitrary vista:
children are guaranteed only once the later level has had the full H4 delay.
-/

namespace Counting.HistoryPrefix

open DirectedCounting PaperHistory

/-- An agent can retain its own earlier information before a temporal path begins. -/
theorem temporalReach_stays {V : Type} (edge : Nat → V → V → Prop)
    (r h : Nat) (source : V) : TemporalReach edge r source h source := by
  induction h with
  | zero => exact .zero
  | succ h ih => exact .stay ih

/-- Extend a causal path backwards by retaining its source's state. -/
theorem temporalReach_prepend_stays {V : Type} (edge : Nat → V → V → Prop)
    (r h d : Nat) (source target : V)
    (path : TemporalReach edge (r + h) source d target) :
    TemporalReach edge r source (h + d) target := by
  induction path with
  | zero => simpa using temporalReach_stays edge r h source
  | stay _ ih => simpa [Nat.add_assoc] using TemporalReach.stay ih
  | send _ hedge ih =>
      exact TemporalReach.send ih (by simpa [Nat.add_assoc] using hedge)

/-- Every visible node carries all of its earlier ancestors into the vista. -/
theorem visible_ancestor {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool) (r h d : Nat)
    (observer : V) (node : Node G leader (r + h))
    (visible : node ∈ visibleNodes G leader (r + h) d observer) :
    CoreHistory.ancestor G leader r (r + h) node ∈
      visibleNodes G leader r (h + d) observer := by
  classical
  obtain ⟨source, hsource, hclass⟩ := Finset.mem_image.mp visible
  apply Finset.mem_image.mpr
  refine ⟨source, ?_, ?_⟩
  · have hp : TemporalReach (fun t u v ↦ 0 < G t u v) (r + h) source d observer := by
      simpa only [causalSupport, Finset.mem_filter, Finset.mem_univ, true_and] using hsource
    have hextended := temporalReach_prepend_stays _ r h d source observer hp
    simpa only [causalSupport, Finset.mem_filter, Finset.mem_univ, true_and] using hextended
  · rw [← hclass, CoreHistory.ancestor_classOf G leader r (r + h) (by omega)]

/-- H1's visible-parent closure at the same observer round. -/
theorem visible_parent {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool) (r d : Nat)
    (observer : V) (node : Node G leader (r + 1))
    (visible : node ∈ visibleNodes G leader (r + 1) d observer) :
    parent G leader r node ∈ visibleNodes G leader r (d + 1) observer := by
  have h := visible_ancestor G leader r 1 d observer node visible
  have heq : CoreHistory.ancestor G leader r (r + 1) node = parent G leader r node := by
    obtain ⟨source, rfl⟩ := Quotient.mk_surjective node
    exact CoreHistory.ancestor_classOf G leader r (r + 1) (by omega) source
  simpa only [heq, Nat.add_comm 1 d] using h

/-- Exhaustiveness at one level makes every preceding level exhaustive. -/
theorem exhaustive_prefix {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool) (r h d : Nat)
    (observer : V)
    (exhaustive : visibleNodes G leader (r + h) d observer = Finset.univ) :
    visibleNodes G leader r (h + d) observer = Finset.univ := by
  classical
  apply Finset.eq_univ_of_forall
  intro node
  have hlater : classOf G leader (r + h) node.out ∈
      visibleNodes G leader (r + h) d observer := by
    rw [exhaustive]
    exact Finset.mem_univ _
  have hearlier := visible_ancestor G leader r h d observer _ hlater
  rw [CoreHistory.ancestor_classOf G leader r (r + h) (by omega), classOf_out] at hearlier
  exact hearlier

/-- Visible-parent closure with every level indexed by one fixed observer round. -/
theorem visible_parent_at_round {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool) (round r : Nat)
    (observer : V) (before : r < round) (node : Node G leader (r + 1))
    (visible : node ∈ visibleNodes G leader (r + 1) (round - (r + 1)) observer) :
    parent G leader r node ∈ visibleNodes G leader r (round - r) observer := by
  have h := visible_parent G leader r (round - (r + 1)) observer node visible
  have heq : round - (r + 1) + 1 = round - r := by omega
  simpa only [heq] using h

/-- Exhaustive-prefix closure with levels indexed by one observer round. -/
theorem exhaustive_prefix_at_round {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool) (round s r : Nat)
    (observer : V) (earlier : s ≤ r) (within : r ≤ round)
    (exhaustive : visibleNodes G leader r (round - r) observer = Finset.univ) :
    visibleNodes G leader s (round - s) observer = Finset.univ := by
  obtain ⟨distance, rfl⟩ := Nat.exists_eq_add_of_le earlier
  have h := exhaustive_prefix G leader s distance (round - (s + distance)) observer exhaustive
  have heq : distance + (round - (s + distance)) = round - s := by omega
  simpa only [heq] using h

/-- A parent has a visible child once the child's level has the full H4 delay.
The conclusion holds for all parent nodes, not just those already visible. -/
theorem visible_child_after_delay {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool)
    (connected : ∀ t, 0 < t → StronglyConnected (fun u v ↦ 0 < G t u v))
    (r d : Nat) (observer : V) (parentNode : Node G leader r)
    (delay : Fintype.card V - 1 ≤ d) :
    ∃ child ∈ visibleNodes G leader (r + 1) d observer,
      parent G leader r child = parentNode := by
  obtain ⟨child, hparent⟩ := forgetMultigraphHistoryClass_surjective G leader r parentNode
  refine ⟨child, ?_, hparent⟩
  rw [vista_level_exhaustive G leader connected (r + 1) d delay observer]
  exact Finset.mem_univ child

end Counting.HistoryPrefix
