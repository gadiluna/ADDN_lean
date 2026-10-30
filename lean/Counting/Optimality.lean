import Counting.LowerCombined

/-!
# Exact optimal round complexity in the distributed model

This joins the verified mathematical local protocol with the three
unconditional indistinguishability constructions. It concerns semantic
correctness and communication rounds. Executable refinement and bit costs
are separate proof obligations.
-/

namespace Counting
open TimingProtocol LowerCombined

/-- The mathematical protocol solves counting at every fixed leader count,
halts simultaneously for the first time at the stated three-case bound,
and no correct protocol can improve that bound for any admissible n,ell. -/
theorem exact_termination_optimal (n ell : Nat) (positive : 1 ≤ ell) (population : ell ≤ n) :
    optimized.SolvesCountingFor ell ∧
    (∀ (V : Type) [Fintype V] (G : Nat → V → V → Nat) (leader : V → Bool),
      Fintype.card V = n → Admissible ell G leader →
        (∀ t, t < optimizedTime n ell → ∀ x,
          ∃ state, optimized.trace ell G leader t x = .active state) ∧
        (∀ x, ∃ state, optimized.trace ell G leader (optimizedTime n ell) x = .halted state n)) ∧
    HardExecution n ell (optimizedTime n ell) := by
  refine ⟨(Protocol.solvesCounting_iff_forall_leaders optimized).mp optimized_solves_counting ell,
    ?_, lower_bound n ell positive population⟩
  intro V finite G leader order valid
  obtain ⟨active, halt⟩ := optimized_simultaneous G leader ell valid
  constructor
  · intro t before x
    exact ⟨_, active t (by simpa only [order] using before) x⟩
  · have halt' : ∀ x, ∃ state,
        optimized.trace ell G leader (optimizedTime (Fintype.card V) ell) x =
          .halted state (Fintype.card V) := fun x => ⟨_, halt x⟩
    simpa only [order] using halt'

end Counting
