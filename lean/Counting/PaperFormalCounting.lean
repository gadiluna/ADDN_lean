import Counting.MachineCountingRuntimeTheorems
import Counting.Optimality

namespace Counting.Paper
open Executable TimingProtocol Machine.CountingRuntime

/-- The complete Core algorithm statement: a fixed executable protocol,
correct simultaneous termination, silent halting, and polynomial total local
finite-tape computation under the stated exponential arc bound. -/
theorem core_algorithm (arcCoefficient arcExponent : Nat) :
    executableCoreProtocol.SolvesCounting ∧
    ∃ coefficient degree,
      ∀ {V : Type} [Fintype V] (G : Nat → V → V → Nat) (leader : V → Bool) (ell : Nat),
        Admissible ell G leader →
        (∀ r,0 < r → r ≤ 2*Fintype.card V →
          arcMass G r ≤ 2^(arcCoefficient*Fintype.card V^arcExponent)) →
        (∀ time,time < 2*Fintype.card V-1 → ∀ observer,
          (binaryCoreNetworkRun G leader ell time observer).output=none) ∧
        (∀ observer,(binaryCoreNetworkRun G leader ell (2*Fintype.card V-1) observer).output=
          some (Fintype.card V)) ∧
        (∀ delay observer,activePhysicalBundles (G (2*Fintype.card V-1+delay+1))
          (binaryCoreNetworkRun G leader ell (2*Fintype.card V-1+delay)) observer=[]) ∧
        (∀ observer,LocalRuntimeBound true G leader ell observer
          (coefficient*(Fintype.card V+1)^degree)) := by
  obtain ⟨coefficient,degree,runtime⟩ :=
    local_runtime_under_polynomial_arc_bound true arcCoefficient arcExponent
  refine ⟨executableCore_solves_counting,coefficient,degree,?_⟩
  intro V inst G leader ell network mass
  exact ⟨fun time before observer=>(binary_core_network_before G leader ell network time before observer).2,
    fun observer=>(binary_core_network_at_stop G leader ell network observer).2,
    fun delay observer=>binary_core_network_silent_after G leader ell network delay observer,
    runtime G leader ell network mass⟩

/-- The complete Exact termination time statement. The lower bound quantifies
over every protocol correct for every admissible population at the fixed
leader count; the upper bound and local runtime refer to the implemented
optimized protocol, including initialization and all live rounds. -/
theorem exact_termination (arcCoefficient arcExponent : Nat) :
    executableProtocol.SolvesCounting ∧
    ∃ coefficient degree,
      ∀ {V : Type} [Fintype V] (G : Nat → V → V → Nat) (leader : V → Bool) (ell : Nat),
        Admissible ell G leader →
        (∀ r,0 < r → r ≤ 2*Fintype.card V →
          arcMass G r ≤ 2^(arcCoefficient*Fintype.card V^arcExponent)) →
        (∀ time,time < optimizedTime (Fintype.card V) ell → ∀ observer,
          (binaryNetworkRun G leader ell time observer).output=none) ∧
        (∀ observer,(binaryNetworkRun G leader ell (optimizedTime (Fintype.card V) ell) observer).output=
          some (Fintype.card V)) ∧
        LowerCombined.HardExecution (Fintype.card V) ell (optimizedTime (Fintype.card V) ell) ∧
        (∀ delay observer,activePhysicalBundles (G (optimizedTime (Fintype.card V) ell+delay+1))
          (binaryNetworkRun G leader ell (optimizedTime (Fintype.card V) ell+delay)) observer=[]) ∧
        (∀ observer,LocalRuntimeBound false G leader ell observer
          (coefficient*(Fintype.card V+1)^degree)) := by
  obtain ⟨coefficient,degree,runtime⟩ :=
    local_runtime_under_polynomial_arc_bound false arcCoefficient arcExponent
  refine ⟨executable_solves_counting,coefficient,degree,?_⟩
  intro V inst G leader ell network mass
  exact ⟨fun time before observer=>(binary_network_before G leader ell network time before observer).2,
    fun observer=>(binary_network_at_stop G leader ell network observer).2,
    LowerCombined.lower_bound _ ell network.positive network.leaderCount_le_card,
    fun delay observer=>binary_network_silent_after G leader ell network delay observer,
    runtime G leader ell network mass⟩

end Counting.Paper

