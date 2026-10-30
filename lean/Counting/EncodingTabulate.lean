import Counting.EncodingNetworkSemantics
import Counting.HistoryRelabel

/-! Executable tabulation of a finite explicitly indexed network into the
same binary-input representation used by the recognition verifier. -/
namespace Counting.Encoding

def tabulate (n t : Nat) (leader : Fin n → Bool) (G : Nat → Fin n → Fin n → Nat) : Simulation.Input :=
  { leaders := Array.ofFn leader
    rounds := Array.ofFn (fun r : Fin t =>
      Array.ofFn (fun a : Fin n => Array.ofFn (G (r.val+1) a))) }

@[simp] theorem tabulate_agents (n t : Nat) (leader : Fin n → Bool)
    (G : Nat → Fin n → Fin n → Nat) : (tabulate n t leader G).leaders.size = n := by
  simp [tabulate]

@[simp] theorem tabulate_rounds (n t : Nat) (leader : Fin n → Bool)
    (G : Nat → Fin n → Fin n → Nat) : (tabulate n t leader G).rounds.size = t := by
  simp [tabulate]

def tabulateEquiv (n t : Nat) (leader : Fin n → Bool) (G : Nat → Fin n → Fin n → Nat) :
    InputAgent (tabulate n t leader G) ≃ Fin n := finCongr (tabulate_agents n t leader G)

theorem tabulate_leader (n t : Nat) (leader : Fin n → Bool) (G : Nat → Fin n → Fin n → Nat)
    (a : InputAgent (tabulate n t leader G)) :
    inputLeader (tabulate n t leader G) a = leader (tabulateEquiv n t leader G a) := by
  simp [inputLeader, tabulate, tabulateEquiv, finCongr]
  rfl

theorem tabulate_matrix (n t : Nat) (leader : Fin n → Bool) (G : Nat → Fin n → Fin n → Nat)
    (r : Fin t) (a b : InputAgent (tabulate n t leader G)) :
    matrixEdge ((tabulate n t leader G).rounds[r.val]'(by rw [tabulate_rounds]; exact r.isLt))
      (tabulate n t leader G).leaders.size a b =
      G (r.val+1) (tabulateEquiv n t leader G a) (tabulateEquiv n t leader G b) := by
  have ha : a.val < n := by simpa using a.isLt
  have hb : b.val < n := by simpa using b.isLt
  simp [tabulate, matrixEdge, tabulateEquiv, finCongr, ha, hb]
  rfl

theorem tabulate_graph (n t : Nat) (leader : Fin n → Bool) (G : Nat → Fin n → Fin n → Nat)
    (r : Nat) (positive : 0 < r) (within : r ≤ t)
    (a b : InputAgent (tabulate n t leader G)) :
    inputGraph (tabulate n t leader G) r a b =
      G r (tabulateEquiv n t leader G a) (tabulateEquiv n t leader G b) := by
  let index : Fin t := ⟨r-1, by omega⟩
  let listed : Fin (tabulate n t leader G).rounds.size := ⟨r-1, by rw [tabulate_rounds]; omega⟩
  have round : listed.val+1 = r := by dsimp [listed]; omega
  rw [← round, inputGraph_listed]
  simpa only [index, listed] using tabulate_matrix n t leader G index a b

theorem tabulate_history (n t : Nat) (leader : Fin n → Bool) (G : Nat → Fin n → Fin n → Nat)
    (r : Nat) (within : r ≤ t) (a : InputAgent (tabulate n t leader G)) :
    history (inputGraph (tabulate n t leader G)) (inputLeader (tabulate n t leader G)) r a =
      history G leader r (tabulateEquiv n t leader G a) :=
  history_equiv (tabulateEquiv n t leader G) _ _ _ _ r
    (tabulate_leader n t leader G)
    (fun round positive bounded => tabulate_graph n t leader G round positive (bounded.trans within)) a

theorem tabulate_leaderCount (n t : Nat) (leader : Fin n → Bool) (G : Nat → Fin n → Fin n → Nat) :
    inputLeaderCount (tabulate n t leader G) = Counting.leaderCount leader :=
  leaderCount_equiv (tabulateEquiv n t leader G) _ _ (tabulate_leader n t leader G)

theorem tabulate_valid (n t : Nat) (leader : Fin n → Bool) (G : Nat → Fin n → Fin n → Nat)
    (population : 0 < n) (leaders : 0 < Counting.leaderCount leader)
    (connected : ∀ r, 0 < r → r ≤ t → DirectedCounting.StronglyConnected (fun a b => 0 < G r a b)) :
    networkValid (tabulate n t leader G) = true := by
  apply (networkValid_iff _).mpr
  refine ⟨by simpa only [tabulate_agents] using population,
    by simpa only [tabulate_leaderCount] using leaders, ?_⟩
  intro round
  let r : Fin t := ⟨round.val, by have := round.isLt; simpa only [tabulate_rounds] using this⟩
  constructor
  · simp only [matrixShape, tabulate, Array.size_ofFn, Array.getElem_ofFn,
      beq_self_eq_true, Bool.true_and]
    simp [Array.all_iff_forall]
  · apply connected_equiv (tabulateEquiv n t leader G) _ (G (r.val+1))
      (tabulate_matrix n t leader G r)
    exact connected (r.val+1) (by omega) (by have := r.isLt; omega)

end Counting.Encoding
