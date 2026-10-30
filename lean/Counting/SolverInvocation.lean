import Counting.CountingSize
import Counting.ExecutableRefinementCorePhysical

/-! Bounds on solver invocations in the actual local programs. SolverPlan is
an executable call representation, not a counter supplied by a caller. This
module counts system calls and variables, not the bit cost of solving them. -/
namespace Counting.Executable
open scoped BigOperators

/-- Every invocation by an audit uses precisely one stored level as its
variable set. This holds also for rejected candidates and solver failures. -/
theorem auditPlan_width (vista : Vista) (ell candidate final width : Nat)
    (called : width ∈ (auditPlan vista ell candidate final).widths) :
    ∃ anchor, width = (levelNodes vista anchor).length := by
  unfold auditPlan at called
  cases found : auditPrefix? vista ell candidate final with
  | none => simp only [found, SolverPlan.widths, List.not_mem_nil] at called
  | some anchor =>
      simp only [found, SolverPlan.widths, List.mem_singleton] at called
      exact ⟨anchor, called⟩

theorem audit_one_system (vista : Vista) (ell candidate final : Nat) :
    (auditPlan vista ell candidate final).widths.length ≤ 1 :=
  SolverPlan.at_most_one _

theorem audit_system_width_le_population {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool) (t : Nat) (observer : V) (vista : Vista)
    (valid : vista.valid = true) (depth : (vista.node vista.bottom).level = t)
    (physical : decodeNode vista t vista.bottom = Counting.history G leader t observer)
    (ell candidate final width : Nat) (called : width ∈ (auditPlan vista ell candidate final).widths) :
    width ≤ Fintype.card V := by
  obtain ⟨anchor, rfl⟩ := auditPlan_width vista ell candidate final width called
  exact levelNodes_length_le_card G leader t observer vista valid depth physical anchor

theorem scheduledPlan_width (ell : Nat) (vista : Vista) (width : Nat)
    (called : width ∈ (scheduledPlan ell vista).widths) :
    ∃ candidate final, width ∈ (auditPlan vista ell candidate final).widths := by
  unfold scheduledPlan at called
  dsimp only at called
  split at called
  · simp only [SolverPlan.widths, List.not_mem_nil] at called
  · cases schedule : candidateAt ell (vista.node vista.bottom).level with
    | none => simp only [schedule, SolverPlan.widths, List.not_mem_nil] at called
    | some pair => exact ⟨pair.1, pair.2, by simpa only [schedule, SolverPlan.widths_map] using called⟩

theorem advance_one_system (state : LocalState) (received : List (Vista × Nat)) (degree : Nat) :
    (advancePlan state received degree).widths.length ≤ 1 := SolverPlan.at_most_one _

/-- The unique possible call is made on the newly updated vista. -/
theorem advancePlan_width (state : LocalState) (received : List (Vista × Nat)) (degree width : Nat)
    (called : width ∈ (advancePlan state received degree).widths) :
    ∃ vista, updateVista? state.vista received degree = some vista ∧
      width ∈ (scheduledPlan state.leaders vista).widths := by
  unfold advancePlan at called
  split at called
  · simp only [SolverPlan.widths, List.not_mem_nil] at called
  · split at called
    · simp only [SolverPlan.widths, List.not_mem_nil] at called
    · cases updated : updateVista? state.vista received degree with
      | none => simp only [updated, SolverPlan.widths, List.not_mem_nil] at called
      | some vista => exact ⟨vista, rfl, by simpa only [updated, SolverPlan.widths_map] using called⟩

/-- During a physical all-active prefix the local implementation calls the
solver at most once and every requested system has at most n variables. -/
theorem physical_round_one_system {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool) (ell t : Nat)
    (states : V → LocalState)
    (represented : ∀ sender, StateRep ell t (Counting.history G leader t sender) (states sender))
    (receiver : V) :
    let plan := advancePlan (states receiver)
      (physicalBundles (G (t+1)) (fun sender => (states sender).vista) receiver)
      (∑ sender, G (t+1) receiver sender)
    plan.widths.length ≤ 1 ∧ ∀ width ∈ plan.widths, width ≤ Fintype.card V := by
  dsimp only
  refine ⟨SolverPlan.at_most_one _, ?_⟩
  intro width called
  obtain ⟨vista, updated, valid, depth, history⟩ := physical_vista_update G leader t
    (fun sender => (states sender).vista) (fun sender => (represented sender).valid)
    (fun sender => (represented sender).level) (fun sender => (represented sender).history) receiver
  obtain ⟨other, otherUpdated, scheduled⟩ := advancePlan_width _ _ _ _ called
  have equal : other = vista := Option.some.inj (otherUpdated.symm.trans updated)
  subst other
  obtain ⟨candidate, final, audit⟩ := scheduledPlan_width _ _ _ scheduled
  exact audit_system_width_le_population G leader (t+1) receiver vista valid depth history
    (states receiver).leaders candidate final width audit

/-- The bound holds at every round of the actual optimized physical run,
including all rounds after simultaneous silent termination. -/
theorem binary_network_one_system {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool) (ell : Nat)
    (network : Counting.Admissible ell G leader) (t : Nat) (receiver : V) :
    let previous := binaryNetworkRun G leader ell t
    let plan := advancePlan (previous receiver)
      (activePhysicalBundles (G (t+1)) previous receiver) (∑ sender, G (t+1) receiver sender)
    plan.widths.length ≤ 1 ∧ ∀ width ∈ plan.widths, width ≤ Fintype.card V := by
  by_cases before : t < Counting.TimingProtocol.optimizedTime (Fintype.card V) ell
  · have prefixRep := binary_network_before G leader ell network t before
    dsimp only
    rw [activePhysicalBundles_of_active _ _ (fun sender => (prefixRep sender).2)]
    exact physical_round_one_system G leader ell t _ (fun sender => (prefixRep sender).1) receiver
  · obtain ⟨delay, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt before)
    dsimp only
    have halted : (binaryNetworkRun G leader ell
        (Counting.TimingProtocol.optimizedTime (Fintype.card V) ell + delay) receiver).output =
          some (Fintype.card V) := by
      rw [binary_network_frozen G leader ell network delay receiver]
      exact (binary_network_at_stop G leader ell network receiver).2
    simp only [advancePlan, halted, Option.isSome_some, if_true,
      SolverPlan.widths, List.length_nil, Nat.zero_le, List.not_mem_nil, false_implies, implies_true, and_self]

/-- The core calendar also chooses one candidate at most. -/
theorem coreScheduledPlan_width (ell : Nat) (vista : Vista) (width : Nat)
    (called : width ∈ (coreScheduledPlan ell vista).widths) :
    ∃ candidate final, width ∈ (auditPlan vista ell candidate final).widths := by
  unfold coreScheduledPlan at called
  dsimp only at called
  split at called
  · exact ⟨_, _, by simpa only [SolverPlan.widths_map] using called⟩
  · simp only [SolverPlan.widths, List.not_mem_nil] at called

theorem advanceCorePlan_width (state : LocalState) (received : List (Vista × Nat)) (degree width : Nat)
    (called : width ∈ (advanceCorePlan state received degree).widths) :
    ∃ vista, updateVista? state.vista received degree = some vista ∧
      width ∈ (coreScheduledPlan state.leaders vista).widths := by
  unfold advanceCorePlan at called
  split at called
  · simp only [SolverPlan.widths, List.not_mem_nil] at called
  · split at called
    · simp only [SolverPlan.widths, List.not_mem_nil] at called
    · cases updated : updateVista? state.vista received degree with
      | none => simp only [updated, SolverPlan.widths, List.not_mem_nil] at called
      | some vista => exact ⟨vista, rfl, by simpa only [updated, SolverPlan.widths_map] using called⟩


theorem physical_core_round_one_system {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool) (ell t : Nat)
    (states : V → LocalState)
    (represented : ∀ sender, StateRep ell t (Counting.history G leader t sender) (states sender))
    (receiver : V) :
    let plan := advanceCorePlan (states receiver)
      (physicalBundles (G (t+1)) (fun sender => (states sender).vista) receiver)
      (∑ sender, G (t+1) receiver sender)
    plan.widths.length ≤ 1 ∧ ∀ width ∈ plan.widths, width ≤ Fintype.card V := by
  dsimp only
  refine ⟨SolverPlan.at_most_one _, ?_⟩
  intro width called
  obtain ⟨vista, updated, valid, depth, history⟩ := physical_vista_update G leader t
    (fun sender => (states sender).vista) (fun sender => (represented sender).valid)
    (fun sender => (represented sender).level) (fun sender => (represented sender).history) receiver
  obtain ⟨other, otherUpdated, scheduled⟩ := advanceCorePlan_width _ _ _ _ called
  have equal : other = vista := Option.some.inj (otherUpdated.symm.trans updated)
  subst other
  obtain ⟨candidate, final, audit⟩ := coreScheduledPlan_width _ _ _ scheduled
  exact audit_system_width_le_population G leader (t+1) receiver vista valid depth history
    (states receiver).leaders candidate final width audit


theorem binary_core_network_one_system {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool) (ell : Nat)
    (network : Counting.Admissible ell G leader) (t : Nat) (receiver : V) :
    let previous := binaryCoreNetworkRun G leader ell t
    let plan := advanceCorePlan (previous receiver)
      (activePhysicalBundles (G (t+1)) previous receiver) (∑ sender, G (t+1) receiver sender)
    plan.widths.length ≤ 1 ∧ ∀ width ∈ plan.widths, width ≤ Fintype.card V := by
  by_cases before : t < (2 * Fintype.card V - 1)
  · have prefixRep := binary_core_network_before G leader ell network t before
    dsimp only
    rw [activePhysicalBundles_of_active _ _ (fun sender => (prefixRep sender).2)]
    exact physical_core_round_one_system G leader ell t _ (fun sender => (prefixRep sender).1) receiver
  · obtain ⟨delay, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt before)
    dsimp only
    have halted : (binaryCoreNetworkRun G leader ell
        ((2 * Fintype.card V - 1) + delay) receiver).output =
          some (Fintype.card V) := by
      rw [binary_core_network_frozen G leader ell network delay receiver]
      exact (binary_core_network_at_stop G leader ell network receiver).2
    simp only [advanceCorePlan, halted, Option.isSome_some, if_true,
      SolverPlan.widths, List.length_nil, Nat.zero_le, List.not_mem_nil, false_implies, implies_true, and_self]

end Counting.Executable
