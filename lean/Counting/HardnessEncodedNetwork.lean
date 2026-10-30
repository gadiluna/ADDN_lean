import Counting.HardnessEncodedEnumeration
import Counting.EncodingTabulate
import Counting.HardnessLeaderReduction
import Counting.EncodingNetworkRecognition

/-! The actual finite matrix input for the X3C baseline construction.
The functions in this file compute concrete arrays and binary output;
the physical relabeling is used only in their correctness proofs. -/
namespace Counting.HardnessEncoded
open Encoding HardnessPath

variable {q m : Nat}

def indexedLeader (q m : Nat) (a : Fin (agents q m).length) : Bool :=
  leader (X3C.baselineGroups q m) (agentEquiv q m a)

def indexedGraph (inst : X3C.Instance q m) (r : Nat)
    (a b : Fin (agents q m).length) : Nat :=
  graph inst r (agentEquiv q m a) (agentEquiv q m b)

def input (inst : X3C.Instance q m) : Simulation.Input :=
  tabulate (agents q m).length (X3C.base q) (indexedLeader q m) (indexedGraph inst)

def inputEquiv (inst : X3C.Instance q m) :
    InputAgent (input inst) ≃ Agent (X3C.baselineGroups q m) :=
  (tabulateEquiv _ _ _ _).trans (agentEquiv q m)

@[simp] theorem input_agents (inst : X3C.Instance q m) :
    (input inst).leaders.size = X3C.baselineMass q m+1 := by
  simp only [input, tabulate_agents, agents_length]

@[simp] theorem input_rounds (inst : X3C.Instance q m) :
    (input inst).rounds.size = X3C.base q := by
  simp only [input, tabulate_rounds]

theorem input_leader (inst : X3C.Instance q m) (a : InputAgent (input inst)) :
    inputLeader (input inst) a = leader (X3C.baselineGroups q m) (inputEquiv inst a) :=
  tabulate_leader _ _ _ _ a

theorem indexed_leaderCount (q m : Nat) : Counting.leaderCount (indexedLeader q m) = 1 :=
  (leaderCount_equiv (agentEquiv q m) _ _ (fun _ => rfl)).trans (leaders _)

@[simp] theorem input_leaderCount (inst : X3C.Instance q m) : inputLeaderCount (input inst) = 1 := by
  rw [input, tabulate_leaderCount, indexed_leaderCount]

theorem input_graph (inst : X3C.Instance q m) (r : Nat) (positive : 0 < r)
    (within : r ≤ X3C.base q) (a b : InputAgent (input inst)) :
    inputGraph (input inst) r a b =
      HardnessBaseline.X3CBaseline.graph inst r (inputEquiv inst a) (inputEquiv inst b) := by
  exact (tabulate_graph _ _ _ _ r positive within a b).trans
    (congrFun (congrFun (congrFun (graph_eq inst) r) _) _)

theorem input_history (inst : X3C.Instance q m) (r : Nat) (within : r ≤ X3C.base q)
    (a : InputAgent (input inst)) :
    history (inputGraph (input inst)) (inputLeader (input inst)) r a =
      history (HardnessBaseline.X3CBaseline.graph inst) (leader (X3C.baselineGroups q m))
        r (inputEquiv inst a) :=
  history_equiv (inputEquiv inst) _ _ _ _ r (input_leader inst)
    (fun round positive bounded => input_graph inst round positive (bounded.trans within)) a

theorem input_valid (inst : X3C.Instance q m) (large : 2 ≤ q) :
    networkValid (input inst) = true := by
  apply tabulate_valid
  · rw [agents_length]; omega
  · rw [indexed_leaderCount]; omega
  · intro r positive _
    apply connected_equiv (agentEquiv q m) _ (HardnessBaseline.X3CBaseline.graph inst r)
    · intro a b
      exact congrFun (congrFun (congrFun (graph_eq inst) r) _) _
    · exact (HardnessBaseline.X3CBaseline.admissible inst large).connected r positive

theorem input_loopless (inst : X3C.Instance q m) (r : Nat) (positive : 0 < r)
    (within : r ≤ X3C.base q) (a : InputAgent (input inst)) :
    inputGraph (input inst) r a a = 0 := by
  rw [input_graph inst r positive within]
  exact HardnessBaseline.X3CBaseline.loopless inst r _

/-- The unique leader is first in the actual serialized population list. -/
def observer (inst : X3C.Instance q m) : InputAgent (input inst) :=
  ⟨0, by rw [input_agents]; omega⟩

@[simp] theorem observer_equiv (inst : X3C.Instance q m) :
    inputEquiv inst (observer inst) = none := rfl

theorem atMostOne_history_time {V : Type} [Fintype V] (ell : Nat)
    (G : Nat → V → V → Nat) (labels : V → Bool) (a : V) {s t : Nat} (same : s = t) :
    Realizability.AtMostOneVista ell (history G labels s a) ↔
      Realizability.AtMostOneVista ell (history G labels t a) := by
  subst t
  rfl

theorem input_atMostOne_iff (inst : X3C.Instance q m) (a : InputAgent (input inst)) :
    Realizability.AtMostOneVista 1 (inputHistory (input inst) a) ↔
      Realizability.AtMostOneVista 1
        (history (HardnessBaseline.X3CBaseline.graph inst) (leader (X3C.baselineGroups q m))
          (X3C.base q) (inputEquiv inst a)) := by
  unfold inputHistory
  rw [atMostOne_history_time _ _ _ _ (input_rounds inst), input_history inst _ le_rfl]

theorem input_knows_iff (inst : X3C.Instance q m) (large : 2 ≤ q) :
    InputSomeAgentKnows (input inst) ↔ ¬ ∃ chosen, inst.IsExactCover chosen := by
  rw [← HardnessReduction.someAgentKnows_iff_noExactCover inst large]
  unfold InputSomeAgentKnows Realizability.SomeAgentKnows
  simp only [input_leaderCount]
  have admissible := networkValid_admissible (input inst) (input_valid inst large)
  rw [input_leaderCount] at admissible
  constructor
  · rintro ⟨_, _, a, knows⟩
    refine ⟨HardnessBaseline.X3CBaseline.admissible inst large, inputEquiv inst a, ?_⟩
    exact (input_atMostOne_iff inst a).mp knows
  · rintro ⟨_, a, knows⟩
    refine ⟨input_valid inst large, admissible, (inputEquiv inst).symm a, ?_⟩
    apply (input_atMostOne_iff inst ((inputEquiv inst).symm a)).mpr
    simpa only [Equiv.apply_symm_apply] using knows

def networkBits (inst : X3C.Instance q m) : List Bool := networkInput.encode (input inst)

theorem networkBits_correct (inst : X3C.Instance q m) (large : 2 ≤ q) :
    BinarySomeAgentKnows (networkBits inst) ↔ ¬ ∃ chosen, inst.IsExactCover chosen := by
  have parsed := (decodeNetwork_iff (networkBits inst) (input inst)).mpr
    ⟨rfl, input_valid inst large⟩
  rw [BinarySomeAgentKnows, parsed]
  exact input_knows_iff inst large

def leaderVista (inst : X3C.Instance q m) : Executable.Vista :=
  agentVista (input inst) (observer inst)

theorem leaderVista_valid (inst : X3C.Instance q m) : (leaderVista inst).valid = true :=
  (inputVistas_correct (input inst) (observer inst)).1

theorem leaderVista_correct (inst : X3C.Instance q m) (large : 2 ≤ q) :
    Realizability.AtMostOneVista 1 (leaderVista inst).denotes ↔
      ¬ ∃ chosen, inst.IsExactCover chosen := by
  have bridge := agentVista_atMostOne_iff (input inst) (observer inst)
  rw [input_leaderCount] at bridge
  change Realizability.AtMostOneVista 1 (agentVista (input inst) (observer inst)).denotes ↔ _
  rw [bridge, input_atMostOne_iff, observer_equiv]
  exact HardnessReduction.atMostOneVista_iff_noExactCover inst large

def vistaBits (inst : X3C.Instance q m) : List Bool := vistaInput.encode (leaderVista inst, 1)

theorem vistaBits_correct (inst : X3C.Instance q m) (large : 2 ≤ q) :
    BinaryAtMostOneVista (vistaBits inst) ↔ ¬ ∃ chosen, inst.IsExactCover chosen := by
  unfold BinaryAtMostOneVista binaryVistaSpectrum vistaBits
  simp only [(vistaInput.decodeExact_iff _ _).mpr rfl]
  rw [Realizability.encodedSpectrum_valid 1 _ (leaderVista_valid inst)]
  exact leaderVista_correct inst large

end Counting.HardnessEncoded
