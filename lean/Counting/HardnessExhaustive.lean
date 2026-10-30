import Counting.ShortAuditView

/-!
# Exhaustiveness forced by the length of an actual visible prefix

The represented population at a visible level is the union of its full
history fibers, not merely the agents in causal support. A proper represented
population strictly shrinks at every succeeding visible level. The last theorem
isolates the cardinality bounds required from the reduction's baseline vista;
it does not assert those bounds for arbitrary vistas.
-/
namespace Counting.HardnessExhaustive
open DirectedCounting PaperHistory

variable {V : Type} [Fintype V]
variable (G : Nat → V → V → Nat) (leader : V → Bool)

noncomputable def represented (round : Nat) (observer : V) (r : Nat) : Finset V :=
  ShortAudit.agents G leader r (CoreTiming.levelsAt G leader round observer r)

@[simp] theorem mem_represented (round : Nat) (observer : V) (r : Nat) (v : V) :
    v ∈ represented G leader round observer r ↔
      classOf G leader r v ∈ CoreTiming.levelsAt G leader round observer r :=
  ShortAudit.mem_agents G leader r _ v

theorem represented_eq_fiber_union [DecidableEq V] (round : Nat) (observer : V) (r : Nat) :
    represented G leader round observer r =
      (CoreTiming.levelsAt G leader round observer r).biUnion (fiber G leader r) := by
  classical
  ext v
  simp only [mem_represented, Finset.mem_biUnion, mem_fiber]
  exact ⟨fun h => ⟨_, h, rfl⟩, fun ⟨_, h, eq⟩ => eq.symm ▸ h⟩

theorem observer_mem_represented (round : Nat) (observer : V) (r : Nat) :
    observer ∈ represented G leader round observer r := by
  apply (mem_represented G leader round observer r observer).mpr
  exact Finset.mem_image.mpr ⟨observer,
    observer_mem_causalSupport G r (round-r) observer, rfl⟩

theorem represented_nonempty (round : Nat) (observer : V) (r : Nat) :
    (represented G leader round observer r).Nonempty :=
  ⟨observer, observer_mem_represented G leader round observer r⟩

/-- Earlier represented populations contain later represented populations at
one fixed observer time. The bound excludes non-level indices above the vista. -/
theorem represented_subset (round : Nat) (observer : V) (r s : Nat)
    (earlier : r ≤ s) (within : s ≤ round) :
    represented G leader round observer s ⊆ represented G leader round observer r := by
  apply ShortAudit.agents_refine G leader r s earlier (CoreTiming.levelsAt G leader round observer)
  intro k hk node visible
  exact HistoryPrefix.visible_parent_at_round G leader round k observer (by omega) node visible

theorem represented_proper (round : Nat) (observer : V) (r s : Nat)
    (earlier : r ≤ s) (within : s ≤ round)
    (proper : represented G leader round observer r ≠ Finset.univ) :
    represented G leader round observer s ≠ Finset.univ := by
  classical
  intro equal
  apply proper
  apply Finset.eq_univ_of_forall
  intro v
  apply represented_subset G leader round observer r s earlier within
  rw [equal]
  exact Finset.mem_univ v

/-- Incoming cut edges force a genuinely missing full fiber at each transition.
The cut head need not be the particular agent witnessing its fiber's visibility. -/
theorem represented_strict_subset (round : Nat) (observer : V) (r : Nat)
    (before : r < round)
    (connected : StronglyConnected (fun a b => 0 < G (r+1) a b))
    (proper : represented G leader round observer r ≠ Finset.univ) :
    represented G leader round observer (r+1) ⊂ represented G leader round observer r := by
  classical
  apply Finset.ssubset_iff_subset_ne.mpr
  exact ⟨represented_subset G leader round observer r (r+1) (by omega) (by omega),
    ShortAudit.agents_strict_refinement G leader round r before observer connected proper⟩

theorem represented_card_drop (round : Nat) (observer : V) (start distance : Nat)
    (within : start + distance ≤ round)
    (connected : ∀ r, start ≤ r → r < start + distance →
      StronglyConnected (fun a b => 0 < G (r+1) a b))
    (proper : represented G leader round observer start ≠ Finset.univ) :
    (represented G leader round observer (start+distance)).card + distance ≤
      (represented G leader round observer start).card := by
  induction distance with
  | zero => simp
  | succ distance ih =>
      have previous := ih (by omega) (fun r hstart hend => connected r hstart (by omega))
      have currentProper := represented_proper G leader round observer start (start+distance)
        (by omega) (by omega) proper
      have strict := represented_strict_subset G leader round observer (start+distance)
        (by omega) (connected _ (by omega) (by omega)) currentProper
      have drop := Finset.card_lt_card strict
      have equal : start + (distance+1) = start+distance+1 := by omega
      rw [equal]
      omega

/-- A visible interval with too little room for one lost agent per round must
start with the entire population. The two endpoint bounds are explicit inputs. -/
theorem exhaustive_of_endpoint_bounds (round : Nat) (observer : V)
    (start distance lower upper : Nat) (within : start+distance ≤ round)
    (connected : ∀ r, start ≤ r → r < start+distance →
      StronglyConnected (fun a b => 0 < G (r+1) a b))
    (initialBound : (represented G leader round observer start).card ≤ upper)
    (finalBound : lower ≤ (represented G leader round observer (start+distance)).card)
    (tooLong : upper < lower+distance) :
    represented G leader round observer start = Finset.univ := by
  classical
  by_contra proper
  have drop := represented_card_drop G leader round observer start distance within connected proper
  omega

theorem represented_exhaustive_iff (round : Nat) (observer : V) (r : Nat) :
    represented G leader round observer r = Finset.univ ↔
      CoreTiming.levelsAt G leader round observer r = Finset.univ := by
  classical
  constructor
  · intro exhaustive
    apply Finset.eq_univ_of_forall
    intro node
    have member : node.out ∈ represented G leader round observer r := by
      rw [exhaustive]
      exact Finset.mem_univ _
    simpa only [mem_represented, classOf_out] using member
  · intro exhaustive
    apply Finset.eq_univ_of_forall
    intro v
    apply (mem_represented G leader round observer r v).mpr
    rw [exhaustive]
    exact Finset.mem_univ _

/-- The first-exhaustive lemma used in the reduction: B=q+3 provides q+1
strict transitions, contradicting |S₁|≤R+q and |S_(B−1)|≥R. -/
theorem first_visible_level_exhaustive (round : Nat) (observer : V) (B q R : Nat)
    (length : B = q+3) (within : B-1 ≤ round)
    (connected : ∀ r, 0 < r → StronglyConnected (fun a b => 0 < G r a b))
    (firstBound : (represented G leader round observer 1).card ≤ R+q)
    (lastBound : R ≤ (represented G leader round observer (B-1)).card) :
    represented G leader round observer 1 = Finset.univ ∧
      CoreTiming.levelsAt G leader round observer 1 = Finset.univ := by
  have equal : 1+(q+1) = B-1 := by omega
  have full := exhaustive_of_endpoint_bounds G leader round observer 1 (q+1) R (R+q)
    (by omega) (fun r _ _ => connected (r+1) (by omega)) firstBound
    (by simpa only [equal] using lastBound) (by omega)
  exact ⟨full, (represented_exhaustive_iff G leader round observer 1).mp full⟩

end Counting.HardnessExhaustive
