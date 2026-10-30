import Counting.ExecutableRefinementProtocol

namespace Counting.Executable
open Counting.TimingProtocolLocal
open scoped BigOperators

/-- The unoptimized core schedule uses at most one solver invocation. -/
def coreScheduledPlan (ell : Nat) (vista : Vista) : SolverPlan (Option Nat) :=
  let depth := (vista.node vista.bottom).level
  let m := (depth + 1) / 2
  if ell ≤ m ∧ depth = 2 * m - 1 then
    (auditPlan vista ell m m).map (fun result => if result.isSome then some m else none)
  else .done none

def coreScheduledOutput (ell : Nat) (vista : Vista) : Option Nat := (coreScheduledPlan ell vista).eval

theorem coreScheduledOutput_unfold (ell : Nat) (vista : Vista) :
    coreScheduledOutput ell vista =
      let depth := (vista.node vista.bottom).level
      let m := (depth+1)/2
      if ell ≤ m ∧ depth = 2*m-1 then
        if (audit? vista ell m m).isSome then some m else none
      else none := by
  unfold coreScheduledOutput coreScheduledPlan
  dsimp only
  split
  · rw [SolverPlan.eval_map]; rfl
  · rfl

/-- Core local transition; a halted state makes no solver calls. -/
def advanceCorePlan (state : LocalState) (received : List (Vista × Nat)) (degree : Nat) :
    SolverPlan (Option LocalState) :=
  if state.output.isSome then .done (some state)
  else if state.leaders == 0 then .done none
  else match updateVista? state.vista received degree with
    | none => .done none
    | some vista => (coreScheduledPlan state.leaders vista).map
        (fun output => some { state with vista := vista, output := output })

def advanceCore? (state : LocalState) (received : List (Vista × Nat))
    (outdegree : Nat) : Option LocalState := (advanceCorePlan state received outdegree).eval

theorem advanceCore_unfold (state : LocalState) (received : List (Vista × Nat)) (degree : Nat) :
    advanceCore? state received degree =
      if state.output.isSome then some state else do
        if state.leaders == 0 then none else do
          let vista ← updateVista? state.vista received degree
          return { state with vista := vista, output := coreScheduledOutput state.leaders vista } := by
  unfold advanceCore? advanceCorePlan
  split
  · rfl
  · split
    · rfl
    · cases updateVista? state.vista received degree with
      | none => rfl
      | some vista => rw [SolverPlan.eval_map]; rfl

theorem coreScheduledOutput_eq_core (ell : Nat) (vista : Vista)
    (valid : vista.valid = true) :
    coreScheduledOutput ell vista = Counting.TimingProtocol.coreDecision ell
      (vista.node vista.bottom).level vista.denotes := by
  classical
  rw [coreScheduledOutput_unfold]
  unfold Counting.TimingProtocol.coreDecision
  dsimp only
  by_cases schedule : ell ≤ ((vista.node vista.bottom).level + 1) / 2 ∧
      (vista.node vista.bottom).level = 2 * (((vista.node vista.bottom).level + 1) / 2) - 1
  · rw [if_pos schedule]
    apply ite_cond_congr
    apply propext
    exact (audit_isSome_iff_pass vista valid ell _ _ (by omega)).trans
      ⟨fun h => ⟨schedule.1, schedule.2, h⟩, fun h => h.2.2⟩
  · have absent : ¬(ell ≤ ((vista.node vista.bottom).level + 1) / 2 ∧
        (vista.node vista.bottom).level = 2 * (((vista.node vista.bottom).level + 1) / 2) - 1 ∧
        Pass ell (((vista.node vista.bottom).level + 1) / 2)
          (((vista.node vista.bottom).level + 1) / 2) (vista.node vista.bottom).level vista.denotes) :=
        fun h => schedule ⟨h.1, h.2.1⟩
    rw [if_neg schedule, if_neg absent]

theorem coreScheduledOutput_history (ell : Nat) (vista : Vista)
    (valid : vista.valid = true) (depth : Nat) (H : Counting.FullHistory depth)
    (level : (vista.node vista.bottom).level = depth)
    (history : decodeNode vista depth vista.bottom = H) :
    coreScheduledOutput ell vista = Counting.TimingProtocol.coreDecision ell depth H := by
  subst depth
  rw [coreScheduledOutput_eq_core ell vista valid]
  exact congrArg (Counting.TimingProtocol.coreDecision ell _) history

theorem advanceCore_halted (state : LocalState) (received : List (Vista × Nat))
    (degree : Nat) (halted : state.output.isSome = true) :
    advanceCore? state received degree = some state := by
  simp [advanceCore_unfold, halted]

theorem advanceCore_active_of_update (state : LocalState) (received : List (Vista × Nat))
    (degree : Nat) (vista : Vista) (active : state.output = none) (positive : 0 < state.leaders)
    (updated : updateVista? state.vista received degree = some vista) :
    advanceCore? state received degree = some { state with
      vista := vista
      output := coreScheduledOutput state.leaders vista } := by
  simp [advanceCore_unfold, active, Nat.ne_of_gt positive, updated]

/-- Recover the actual DAG result from a successful active optimized step;
its construction is shared verbatim by the core step. -/
theorem advance_active_update (state : LocalState) (received : List (Vista × Nat))
    (degree : Nat) (next : LocalState) (active : state.output = none)
    (success : advance? state received degree = some next) :
    updateVista? state.vista received degree = some next.vista := by
  by_cases zero : state.leaders = 0
  · simp [advance_unfold, active, zero] at success
  · cases updated : updateVista? state.vista received degree with
    | none => simp [advance_unfold, active, zero, updated] at success
    | some vista =>
      rw [advance_active_of_update state received degree vista active (Nat.pos_of_ne_zero zero) updated] at success
      have equal := Option.some.inj success
      exact congrArg (fun state : LocalState => some state.vista) equal

/-- The executable core in the anonymous silent-halting protocol interface.
As for the optimized wrapper, packet expansion here is only the mathematical
multiset adapter; the local function accepts binary multiplicity bundles. -/
noncomputable def executableCoreProtocol : Counting.Protocol LocalState where
  init := initialState
  update := fun state messages degree => (advanceCore? state (protocolPackets messages) degree).getD state
  out := fun state _ => state.output

/-- Physical core update: the exact DAG and Gaussian audit produce the
mathematical core decision on the agent's complete received history. -/
theorem core_update_physical {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool) (ell depth : Nat) (positive : 0 < ell)
    (states : V → LocalState)
    (represented : ∀ x, StateRep ell depth (Counting.history G leader depth x) (states x))
    (active : ∀ x, (states x).output = none) (receiver : V) :
    ∃ next, advanceCore? (states receiver)
        (protocolPackets (Counting.incoming (G (depth + 1)) states receiver))
        (∑ sender, G (depth + 1) receiver sender) = some next ∧
      StateRep ell (depth + 1) (Counting.history G leader (depth + 1) receiver) next ∧
      next.output = Counting.TimingProtocol.coreDecision ell (depth + 1)
        (Counting.history G leader (depth + 1) receiver) := by
  obtain ⟨optimized, success, rep, _⟩ := executable_update_physical G leader ell depth positive
    states represented active receiver
  have updated := advance_active_update _ _ _ _ (active receiver) success
  have output := coreScheduledOutput_history ell optimized.vista rep.valid (depth + 1)
    (Counting.history G leader (depth + 1) receiver) rep.level rep.history
  let next : LocalState := { states receiver with
    vista := optimized.vista
    output := Counting.TimingProtocol.coreDecision ell (depth + 1)
      (Counting.history G leader (depth + 1) receiver) }
  refine ⟨next, ?_, ⟨(represented receiver).leaderCount, rep.valid, rep.level, rep.history⟩, rfl⟩
  rw [advanceCore_active_of_update _ _ _ _ (active receiver)
    (by rw [(represented receiver).leaderCount]; exact positive) updated,
    (represented receiver).leaderCount, output]
  simp only [next, (represented receiver).leaderCount]

theorem core_trace_step {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool) (ell depth : Nat) (positive : 0 < ell)
    (states : V → LocalState)
    (represented : ∀ x, StateRep ell depth (Counting.history G leader depth x) (states x))
    (active : ∀ x, (states x).output = none)
    (trace : ∀ x, executableCoreProtocol.trace ell G leader depth x = .active (states x)) (receiver : V) :
    ∃ next, StateRep ell (depth + 1) (Counting.history G leader (depth + 1) receiver) next ∧
      next.output = Counting.TimingProtocol.coreDecision ell (depth + 1)
        (Counting.history G leader (depth + 1) receiver) ∧
      executableCoreProtocol.trace ell G leader (depth + 1) receiver =
        match next.output with
        | none => .active next
        | some n => .halted next n := by
  obtain ⟨next, updated, rep, output⟩ := core_update_physical G leader ell depth positive
    states represented active receiver
  refine ⟨next, rep, output, ?_⟩
  have all : executableCoreProtocol.trace ell G leader depth = fun x => Counting.Status.active (states x) := funext trace
  rw [Counting.Protocol.trace, all, Counting.TimingProtocol.active_messages]
  simp only [Counting.Protocol.advance, executableCoreProtocol, updated, Option.getD_some]
  rfl

end Counting.Executable
