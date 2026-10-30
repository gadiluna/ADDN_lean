import Counting.DagSemanticsValidityIteration
import Counting.DagSemanticsView
import Counting.TimingProtocolCorrectness
import Counting.ExecutableRefinementEquivalence

namespace Counting.Executable
open Counting.TimingProtocolLocal

/-- One leader schedules exactly the core audit of candidates m>1. -/
theorem candidateAt_one_iff (round m final : Nat) :
    candidateAt 1 round = some (m, final) ↔ 1 < m ∧ round = 2*m-1 ∧ final = m := by
  simp only [candidateAt, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
  split_ifs <;> simp_all <;> omega

/-- At least two leaders schedule exactly the short audit of candidates m>ell. -/
theorem candidateAt_many_iff (ell round m final : Nat) (many : 2 ≤ ell) :
    candidateAt ell round = some (m, final) ↔ ell < m ∧ round = 2*m-2 ∧ final = m-1 := by
  simp only [candidateAt, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
  split_ifs <;> simp_all <;> omega

@[simp] theorem candidateAt_early (ell round : Nat) (early : round ≤ ell) :
    candidateAt ell round = none := by simp [candidateAt, early]

@[simp] theorem candidateAt_zero (round : Nat) : candidateAt 0 round = none := by
  simp [candidateAt]

/-- The arithmetic scheduler is the one used by the semantic decisions;
the all-leaders round is reserved for its separate early test. -/
theorem candidateAt_eq_semantic_schedule (ell round : Nat) (positive : 0 < ell) :
    candidateAt ell round =
      if round = ell then none else
      if ell = 1 then
        let m := (round+1)/2
        if ell ≤ m ∧ round = 2*m-1 then some (m, m) else none
      else
        let m := round/2+1
        if ell < m ∧ round = 2*m-2 then some (m, m-1) else none := by
  by_cases equal : round = ell
  · subst round
    simp
  by_cases one : ell = 1
  · subst ell
    simp only [equal, if_false, if_true]
    by_cases schedule : 1 ≤ (round+1)/2 ∧ round = 2*((round+1)/2)-1
    · rw [if_pos schedule]
      apply (candidateAt_one_iff _ _ _).mpr
      exact ⟨by omega, schedule.2, rfl⟩
    · rw [if_neg schedule]
      cases outcome : candidateAt 1 round with
      | none => rfl
      | some pair =>
          have values := (candidateAt_one_iff round pair.1 pair.2).mp outcome
          exfalso
          apply schedule
          omega
  · simp only [equal, one, if_false]
    by_cases schedule : ell < round/2+1 ∧ round = 2*(round/2+1)-2
    · rw [if_pos schedule]
      exact (candidateAt_many_iff ell round _ _ (by omega)).mpr ⟨schedule.1, schedule.2, rfl⟩
    · rw [if_neg schedule]
      cases outcome : candidateAt ell round with
      | none => rfl
      | some pair =>
          have values := (candidateAt_many_iff ell round pair.1 pair.2 (by omega)).mp outcome
          exfalso
          apply schedule
          omega

/-- The actual level-zero scan is exactly absence of a nonleader history. -/
theorem all_leaders_scan_iff (vista : Vista) (valid : vista.valid = true) :
    (!(levelNodes vista 0).any (fun i => !(vista.node i).leader)) = true ↔
      false ∉ levels (vista.node vista.bottom).level vista.denotes 0 := by
  have seen : false ∈ decodedLevel vista 0 ↔
      ∃ i ∈ levelNodes vista 0, (vista.node i).leader = false := by
    constructor
    · intro visible
      obtain ⟨i, inside, level, equal⟩ := (mem_decodedLevel vista 0 false).mp visible
      refine ⟨i, ?_, equal⟩
      simpa only [levelNodes, List.mem_filter, List.mem_range, beq_iff_eq] using And.intro inside level
    · rintro ⟨i, member, equal⟩
      have fields : i < vista.nodes.size ∧ (vista.node i).level = 0 := by
        simpa only [levelNodes, List.mem_filter, List.mem_range, beq_iff_eq] using member
      exact (mem_decodedLevel vista 0 false).mpr ⟨i, fields.1, fields.2, equal⟩
  rw [← decodedLevel_eq_levels vista valid, seen]
  simp only [Bool.not_eq_true', List.any_eq_false, not_exists, not_and]

/-- The pure output expression is the expression evaluated by advance?. -/
def scheduledOutput (ell : Nat) (vista : Vista) : Option Nat :=
  let round := (vista.node vista.bottom).level
  if round == ell && !(levelNodes vista 0).any (fun i => !(vista.node i).leader) then some ell
  else match candidateAt ell round with
    | none => none
    | some (candidate, last) => if (audit? vista ell candidate last).isSome then some candidate else none

/-- This bridge only requires the separate audit correctness theorem. It does
not replace the executable checker with an oracle or change its control flow. -/
theorem scheduledOutput_eq_optimized (ell : Nat) (vista : Vista)
    (positive : 0 < ell) (valid : vista.valid = true)
    (auditCorrect : ∀ (m final : Nat) (_within : final ≤ (vista.node vista.bottom).level),
      (audit? vista ell m final).isSome = true ↔
        Pass ell m final (vista.node vista.bottom).level vista.denotes) :
    scheduledOutput ell vista =
      Counting.TimingProtocol.optimizedDecision ell (vista.node vista.bottom).level vista.denotes := by
  classical
  have initialTest := all_leaders_scan_iff vista valid
  unfold scheduledOutput Counting.TimingProtocol.optimizedDecision
  dsimp only
  rw [candidateAt_eq_semantic_schedule ell _ positive]
  simp only [Bool.and_eq_true, beq_iff_eq, initialTest]
  by_cases equal : (vista.node vista.bottom).level = ell
  · simp only [equal, if_true, true_and]
  · simp only [equal, false_and, if_false]
    by_cases one : ell = 1
    · simp only [if_pos one, Counting.TimingProtocol.coreDecision]
      by_cases schedule : ell ≤ ((vista.node vista.bottom).level+1)/2 ∧
          (vista.node vista.bottom).level = 2*(((vista.node vista.bottom).level+1)/2)-1
      · rw [if_pos schedule]
        apply ite_cond_congr
        apply propext
        exact (auditCorrect _ _ (by omega)).trans
          ⟨fun h => ⟨schedule.1, schedule.2, h⟩, fun h => h.2.2⟩
      · have absent : ¬(ell ≤ ((vista.node vista.bottom).level+1)/2 ∧
            (vista.node vista.bottom).level = 2*(((vista.node vista.bottom).level+1)/2)-1 ∧
            Pass ell (((vista.node vista.bottom).level+1)/2) (((vista.node vista.bottom).level+1)/2)
              (vista.node vista.bottom).level vista.denotes) :=
          fun h => schedule ⟨h.1, h.2.1⟩
        rw [if_neg schedule, if_neg absent]
    · simp only [if_neg one, Counting.TimingProtocol.shortDecision]
      by_cases schedule : ell < (vista.node vista.bottom).level/2+1 ∧
          (vista.node vista.bottom).level = 2*((vista.node vista.bottom).level/2+1)-2
      · rw [if_pos schedule]
        apply ite_cond_congr
        apply propext
        exact (auditCorrect _ _ (by omega)).trans
          ⟨fun h => ⟨schedule.1, schedule.2, h⟩, fun h => h.2.2⟩
      · have absent : ¬(ell < (vista.node vista.bottom).level/2+1 ∧
            (vista.node vista.bottom).level = 2*((vista.node vista.bottom).level/2+1)-2 ∧
            Pass ell ((vista.node vista.bottom).level/2+1) ((vista.node vista.bottom).level/2+1-1)
              (vista.node vista.bottom).level vista.denotes) :=
          fun h => schedule ⟨h.1, h.2.1⟩
        rw [if_neg schedule, if_neg absent]

theorem advance_active_of_update (state : LocalState) (received : List (Vista × Nat))
    (outdegree : Nat) (next : Vista) (active : state.output = none) (positive : 0 < state.leaders)
    (success : updateVista? state.vista received outdegree = some next) :
    advance? state received outdegree =
      some {state with vista := next, output := scheduledOutput state.leaders next} := by
  have nonzero : state.leaders ≠ 0 := Nat.ne_of_gt positive
  simp [advance_unfold, active, nonzero, success, scheduledOutput]
  rfl

/-- Every accepted nonhalting transition produces a valid new local vista. -/
theorem advance_active_valid (state : LocalState) (received : List (Vista × Nat))
    (outdegree : Nat) (next : LocalState) (active : state.output = none)
    (success : advance? state received outdegree = some next) : next.vista.valid = true := by
  by_cases zero : state.leaders = 0
  · simp [advance_unfold, active, zero] at success
  · have positive : 0 < state.leaders := Nat.pos_of_ne_zero zero
    cases updated : updateVista? state.vista received outdegree with
    | none => simp [advance_unfold, active, zero, updated] at success
    | some vista =>
        rw [advance_active_of_update state received outdegree vista active positive updated] at success
        have equal := Option.some.inj success
        rw [← equal]
        exact updateVista_valid _ _ _ _ updated

/-- The executable initial scan detects exactly n=ell on an admissible actual
history, with no population size supplied to the program. -/
theorem all_leaders_scan_actual_iff {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool) (ell : Nat)
    (network : Counting.Admissible ell G leader) (observer : V) (vista : Vista)
    (valid : vista.valid = true) (level : (vista.node vista.bottom).level = ell)
    (history : decodeNode vista ell vista.bottom = Counting.history G leader ell observer) :
    (!(levelNodes vista 0).any (fun i => !(vista.node i).leader)) = true ↔
      Fintype.card V = ell := by
  subst ell
  rw [all_leaders_scan_iff vista valid]
  change (false ∉ levels (vista.node vista.bottom).level
    (decodeNode vista (vista.node vista.bottom).level vista.bottom) 0) ↔ _
  rw [history]
  exact Counting.TimingProtocol.local_all_leaders_iff G leader _ observer network

/-- The concrete active transition has the same output as the mathematical
optimized decision once the audit equivalence is supplied. -/
theorem advance_active_refines (state : LocalState) (received : List (Vista × Nat))
    (outdegree : Nat) (vista : Vista) (active : state.output = none) (positive : 0 < state.leaders)
    (updated : updateVista? state.vista received outdegree = some vista)
    (auditCorrect : ∀ (m final : Nat) (_within : final ≤ (vista.node vista.bottom).level),
      (audit? vista state.leaders m final).isSome = true ↔
        Pass state.leaders m final (vista.node vista.bottom).level vista.denotes) :
    advance? state received outdegree = some {state with
      vista := vista
      output := Counting.TimingProtocol.optimizedDecision state.leaders
        (vista.node vista.bottom).level vista.denotes} := by
  rw [advance_active_of_update state received outdegree vista active positive updated,
    scheduledOutput_eq_optimized state.leaders vista positive
      (updateVista_valid _ _ _ _ updated) auditCorrect]

theorem advance_valid (state : LocalState) (received : List (Vista × Nat))
    (outdegree : Nat) (next : LocalState) (valid : state.vista.valid = true)
    (success : advance? state received outdegree = some next) : next.vista.valid = true := by
  cases output : state.output with
  | none => exact advance_active_valid state received outdegree next output success
  | some value =>
      rw [advance_halted state received outdegree (by simp [output])] at success
      exact Option.some.inj success ▸ valid

/-- Active execution is total on the same valid input interface as its updater. -/
theorem advance_active_total (state : LocalState) (received : List (Vista × Nat)) (outdegree : Nat)
    (active : state.output = none) (positive : 0 < state.leaders) (valid : state.vista.valid = true)
    (receivedValid : ∀ message ∈ received, message.1.valid = true ∧ 0 < message.2 ∧
      (message.1.node message.1.bottom).level = (state.vista.node state.vista.bottom).level) :
    ∃ next, advance? state received outdegree = some next ∧ next.vista.valid = true ∧
      next.leaders = state.leaders ∧
      (next.vista.node next.vista.bottom).level = (state.vista.node state.vista.bottom).level + 1 := by
  obtain ⟨vista, updated, vistaValid, level⟩ := updateVista_total state.vista received outdegree valid receivedValid
  exact ⟨_, advance_active_of_update state received outdegree vista active positive updated,
    vistaValid, rfl, level⟩

/-- The implemented decision, including the Gaussian-backed audit, agrees
with the mathematical optimized decision on every valid vista. -/
theorem scheduledOutput_optimized (ell : Nat) (vista : Vista)
    (positive : 0 < ell) (valid : vista.valid = true) :
    scheduledOutput ell vista =
      Counting.TimingProtocol.optimizedDecision ell (vista.node vista.bottom).level vista.denotes :=
  scheduledOutput_eq_optimized ell vista positive valid
    (fun m final within => audit_isSome_iff_pass vista valid ell m final within)

/-- No conditional audit premise remains in the active local transition bridge. -/
theorem advance_active_optimized (state : LocalState) (received : List (Vista × Nat))
    (outdegree : Nat) (vista : Vista) (active : state.output = none) (positive : 0 < state.leaders)
    (updated : updateVista? state.vista received outdegree = some vista) :
    advance? state received outdegree = some {state with
      vista := vista
      output := Counting.TimingProtocol.optimizedDecision state.leaders
        (vista.node vista.bottom).level vista.denotes} :=
  advance_active_refines state received outdegree vista active positive updated
    (fun m final within => audit_isSome_iff_pass vista (updateVista_valid _ _ _ _ updated)
      state.leaders m final within)

end Counting.Executable
