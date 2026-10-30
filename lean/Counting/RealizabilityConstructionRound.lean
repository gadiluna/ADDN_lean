import Counting.RealizabilityConstructionConnected
import Counting.RealizabilityConstructionMany
import Counting.RealizabilityConstructionHistory

namespace Counting.RealizabilityConstruction.RoundData
open DirectedCounting
variable {A U W : Type*} [Fintype A] [Nonempty A] [Fintype U]
    [Nonempty U] [DecidableEq U] [Nonempty W] (d : RoundData A U W)

/-- A strongly connected physical round with the prescribed selected
outdegrees and old-type receipts, after all auxiliary vertices are removed.
Previously unselected agents send no arcs into the new selected set. -/
theorem physical_round_exists (balance : d.Balanced)
    (newNonempty : ∀ v, ∃ a, d.new a = some v)
    (connected : StronglyConnected d.typeArc) :
    ∃ E : A → A → Nat,
      StronglyConnected (fun x y => 0 < E x y) ∧
      (∀ a v, d.new a = some v → (∑ b : A, E a b) = d.degree v) ∧
      (∀ a v, d.new a = some v → ∀ u,
        (∑ b : A, if d.old b = some u then E b a else 0) = d.red u v) ∧
      (∀ a v, d.new a = some v → ∀ b, d.old b = none → E b a = 0) := by
  classical
  obtain ⟨E, sc, degrees, receipts, untouched⟩ := eliminate_independent_auxiliaries
    d.expanded d.old d.expanded_aux_loopless (d.expanded_balanced balance)
    (d.expanded_connected newNonempty connected) d.expanded_tails_typed
  refine ⟨E, sc, ?_, ?_, ?_⟩
  · intro a v selected
    exact (degrees a).trans (d.expanded_selected_outdegree a v selected)
  · intro a v selected u
    rw [receipts u a, d.expanded_selected_receipt u a v selected]
    have zero : ∀ b, d.expanded (.inl b) (.inl a) = 0 := by
      intro b
      simp [expanded, outsideArc, selected]
    simp only [zero, ite_self, Finset.sum_const_zero, Nat.zero_add]
  · intro a v selected b old
    rw [untouched b old a]
    simp [expanded, outsideArc, selected]

end Counting.RealizabilityConstruction.RoundData
