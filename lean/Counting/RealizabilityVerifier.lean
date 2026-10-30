import Counting.DagSemanticsTransport
import Counting.RealizabilityCertificate
import Counting.RealizabilityVerifierGraph

namespace Counting.RealizabilityVerifier
open Counting.Executable

abbrev LevelIndex (vista : Vista) (r : ℕ) :=
  {i : Fin vista.nodes.size // (vista.node i.val).level = r}

def weight (weights : Array ℕ) (i : ℕ) : ℕ := weights[i]?.getD 0

def childCount (vista : Vista) (weights : Array ℕ) (r old : ℕ) : ℕ :=
  ((children vista old (r + 1)).map (weight weights)).sum

def leaving (vista : Vista) (weights : Array ℕ) (r old : ℕ) : ℕ :=
  weight weights old - childCount vista weights r old

def supply (vista : Vista) (weights : Array ℕ) (r old : ℕ) : ℕ :=
  ((children vista old (r + 1)).map (fun i => weight weights i * (vista.node i).degree)).sum

def demand (vista : Vista) (weights : Array ℕ) (r old : ℕ) : ℕ :=
  ((levelNodes vista (r + 1)).map (fun i => weight weights i * countFrom (vista.node i) old)).sum

def hidden (N : ℕ) (vista : Vista) (weights : Array ℕ) (r : ℕ) : ℕ :=
  N - ((levelNodes vista (r + 1)).map (weight weights)).sum

def initialCount (vista : Vista) (weights : Array ℕ) (b : Bool) : ℕ :=
  ((levelNodes vista 0).map (fun i => if (vista.node i).leader = b then weight weights i else 0)).sum

def outsideSize (N : ℕ) (vista : Vista) (weights : Array ℕ) (r : ℕ) : ℕ :=
  if 0 < hidden N vista weights r then 1 else 0

abbrev RoundVertex (N : ℕ) (vista : Vista) (weights : Array ℕ) (r : ℕ) :=
  LevelIndex vista (r + 1) ⊕ (LevelIndex vista r ⊕ Fin (outsideSize N vista weights r))

def roundArc (N : ℕ) (vista : Vista) (weights : Array ℕ) (r : ℕ) :
    RoundVertex N vista weights r → RoundVertex N vista weights r → Bool
  | .inl v, .inr (.inl u) =>
      (vista.node v.val.val).parent == some u.val.val && 0 < (vista.node v.val.val).degree
  | .inr (.inl u), .inl v => 0 < countFrom (vista.node v.val.val) u.val.val
  | .inr (.inr _), .inr (.inl u) => 0 < leaving vista weights r u.val.val
  | .inr (.inl u), .inr (.inr _) =>
      0 < leaving vista weights r u.val.val || demand vista weights r u.val.val < supply vista weights r u.val.val
  | _, _ => false

/-- Every operation is over DAG node indices or binary natural counts.
The auxiliary connectivity check never expands the claimed population. -/
def verify (vista : Vista) (weights : Array ℕ) (ell N : ℕ) : Bool :=
  vista.valid && weights.size == vista.nodes.size && decide (
    0 < ell ∧ ell ≤ N ∧
    (∀ i : Fin vista.nodes.size, 0 < weight weights i.val) ∧
    weight weights vista.bottom = 1 ∧
    initialCount vista weights true ≤ ell ∧
    initialCount vista weights false ≤ N - ell ∧
    ∀ r : Fin (vista.node vista.bottom).level,
      (∀ u : LevelIndex vista r.val, childCount vista weights r.val u.val.val ≤ weight weights u.val.val) ∧
      (hidden N vista weights r.val = 0 → ∀ u : LevelIndex vista r.val,
        supply vista weights r.val u.val.val = demand vista weights r.val u.val.val) ∧
      (0 < hidden N vista weights r.val → ∀ u : LevelIndex vista r.val,
        leaving vista weights r.val u.val.val = 0 →
          demand vista weights r.val u.val.val ≤ supply vista weights r.val u.val.val) ∧
      (1 < N → connectedCheck (roundArc N vista weights r.val) = true))

structure Checks (vista : Vista) (weights : Array ℕ) (ell N : ℕ) : Prop where
  valid : vista.valid = true
  length : weights.size = vista.nodes.size
  leaders_positive : 0 < ell
  order_ge_leaders : ell ≤ N
  positive : ∀ i : Fin vista.nodes.size, 0 < weight weights i.val
  bottom_one : weight weights vista.bottom = 1
  initial_leaders : initialCount vista weights true ≤ ell
  initial_nonleaders : initialCount vista weights false ≤ N - ell
  refinement : ∀ r, r < (vista.node vista.bottom).level → ∀ u : LevelIndex vista r,
    childCount vista weights r u.val.val ≤ weight weights u.val.val
  balance_full : ∀ r, r < (vista.node vista.bottom).level → hidden N vista weights r = 0 →
    ∀ u : LevelIndex vista r, supply vista weights r u.val.val = demand vista weights r u.val.val
  balance_no_leaving : ∀ r, r < (vista.node vista.bottom).level → 0 < hidden N vista weights r →
    ∀ u : LevelIndex vista r, leaving vista weights r u.val.val = 0 →
      demand vista weights r u.val.val ≤ supply vista weights r u.val.val
  connected : ∀ r, r < (vista.node vista.bottom).level → 1 < N →
    DirectedCounting.StronglyConnected (fun u v => roundArc N vista weights r u v = true)

theorem verify_iff_checks (vista : Vista) (weights : Array ℕ) (ell N : ℕ) :
    verify vista weights ell N = true ↔ Checks vista weights ell N := by
  simp only [verify, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨valid, length⟩, leaders, order, positive, bottom, leaderCount, nonleaderCount, rounds⟩
    refine ⟨valid, length, leaders, order, positive, bottom, leaderCount, nonleaderCount,
      ?_, ?_, ?_, ?_⟩
    · intro r hr; exact (rounds ⟨r, hr⟩).1
    · intro r hr; exact (rounds ⟨r, hr⟩).2.1
    · intro r hr; exact (rounds ⟨r, hr⟩).2.2.1
    · intro r hr hn
      exact (connectedCheck_iff _).mp ((rounds ⟨r, hr⟩).2.2.2 hn)
  · intro checks
    refine ⟨⟨checks.valid, checks.length⟩, checks.leaders_positive, checks.order_ge_leaders,
      checks.positive, checks.bottom_one, checks.initial_leaders, checks.initial_nonleaders, ?_⟩
    intro r
    exact ⟨checks.refinement r.val r.isLt, checks.balance_full r.val r.isLt,
      checks.balance_no_leaving r.val r.isLt,
      fun hn => (connectedCheck_iff _).mpr (checks.connected r.val r.isLt hn)⟩

end Counting.RealizabilityVerifier
