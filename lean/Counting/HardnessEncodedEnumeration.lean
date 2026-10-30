import Counting.HardnessBaselineGraph
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.ProdSigma

/-! Explicit computable enumeration and edge functions for the baseline
hardness network. Physical agent names are used only by the offline input
constructor, never by the anonymous protocol. -/
namespace Counting.HardnessEncoded
open HardnessPath

def groups (m : Nat) : List (Option (Fin m)) := none :: (List.finRange m).map some

theorem groups_nodup (m : Nat) : (groups m).Nodup := by
  rw [groups, List.nodup_cons]
  exact ⟨by simp, List.Nodup.map (Option.some_injective _) (List.nodup_finRange m)⟩

theorem groups_complete (m : Nat) (group : Option (Fin m)) : group ∈ groups m := by
  cases group <;> simp [groups]

def agents (q m : Nat) : List (Agent (X3C.baselineGroups q m)) :=
  none :: ((groups m).sigma (fun group => List.finRange (X3C.baselineGroups q m group))).map some

theorem agents_nodup (q m : Nat) : (agents q m).Nodup := by
  rw [agents, List.nodup_cons]
  constructor
  · simp
  · exact List.Nodup.map (Option.some_injective _)
      ((groups_nodup m).sigma (fun group => List.nodup_finRange _))

theorem agents_complete (q m : Nat) (agent : Agent (X3C.baselineGroups q m)) :
    agent ∈ agents q m := by
  cases agent with
  | none => exact List.mem_cons_self
  | some member =>
      rcases member with ⟨group, position⟩
      apply List.mem_cons_of_mem
      apply List.mem_map.mpr
      exact ⟨⟨group, position⟩, List.mem_sigma.mpr ⟨groups_complete m group, List.mem_finRange position⟩, rfl⟩

/-- This equivalence uses the explicit list and executable index search;
it does not choose a noncomputable ordering of a quotient or a finite set. -/
def agentEquiv (q m : Nat) : Fin (agents q m).length ≃ Agent (X3C.baselineGroups q m) :=
  (agents_nodup q m).getEquivOfForallMemList _ (agents_complete q m)

theorem agents_length (q m : Nat) : (agents q m).length = X3C.baselineMass q m+1 := by
  have equal := Fintype.card_congr (agentEquiv q m)
  simpa only [Fintype.card_fin, HardnessBaseline.X3CBaseline.order] using equal

theorem agentEquiv_zero (q m : Nat) :
    agentEquiv q m ⟨0, by simp [agents]⟩ = none := rfl

def pathEdge {q m : Nat} (inst : X3C.Instance q m) :
    Agent (X3C.baselineGroups q m) → Agent (X3C.baselineGroups q m) → Nat
  | none, none => 0
  | none, some target => inst.coefficient target.1
  | some source, target => if next (X3C.baselineGroups q m) source = target then 1 else 0

def starEdge {q m : Nat} (inst : X3C.Instance q m) :
    Agent (X3C.baselineGroups q m) → Agent (X3C.baselineGroups q m) → Nat
  | none, none => 0
  | none, some target => inst.coefficient target.1
  | some _, none => 1
  | some _, some _ => 0

theorem pathEdge_eq {q m : Nat} (inst : X3C.Instance q m) :
    pathEdge inst = edge inst.coefficient (X3C.baselineGroups q m) := by
  funext source target
  cases source <;> cases target <;> simp [pathEdge, edge]

theorem starEdge_eq {q m : Nat} (inst : X3C.Instance q m) :
    starEdge inst = star inst.coefficient (X3C.baselineGroups q m) := by
  funext source target
  cases source <;> cases target <;> rfl

def graph {q m : Nat} (inst : X3C.Instance q m) (round : Nat) :
    Agent (X3C.baselineGroups q m) → Agent (X3C.baselineGroups q m) → Nat :=
  if round < X3C.base q then pathEdge inst else starEdge inst

theorem graph_eq {q m : Nat} (inst : X3C.Instance q m) :
    graph inst = HardnessBaseline.X3CBaseline.graph inst := by
  funext round
  simp only [graph, HardnessBaseline.X3CBaseline.graph, HardnessBaseline.network,
    pathEdge_eq, starEdge_eq]

end Counting.HardnessEncoded
