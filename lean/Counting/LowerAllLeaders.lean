import Counting.Network
import DirectedCountingFormalization.Connectivity

/-!
# The all-leaders path lower bound

The smaller static bidirected path has `k+1` leaders. The larger path adds
one nonleader at the far endpoint. Late outdegree awareness preserves each
corresponding vertex's history while `vertex + time ≤ k`, including the
singleton case at time zero.
-/

namespace Counting.LowerAllLeaders

open DirectedCounting
open scoped BigOperators

/-- Unit-multiplicity bidirected path; no loops. -/
def edge (n : Nat) (u v : Fin n) : Nat :=
  if u.val + 1 = v.val ∨ v.val + 1 = u.val then 1 else 0

def network (n : Nat) : Nat → Fin n → Fin n → Nat := fun _ ↦ edge n

def allLeaders (k : Nat) : Fin (k + 1) → Bool := fun _ ↦ true

def extendedLeaders (k : Nat) (v : Fin (k + 1 + 1)) : Bool :=
  decide (v.val < k + 1)

@[simp] theorem edge_castSucc (n : Nat) (u v : Fin n) :
    edge (n + 1) u.castSucc v.castSucc = edge n u v := rfl

@[simp] theorem extendedLeaders_castSucc (k : Nat) (v : Fin (k + 1)) :
    extendedLeaders k v.castSucc = true := by
  simp [extendedLeaders, v.isLt]

/-- Every finite nonempty bidirected path is strongly connected. -/
theorem path_stronglyConnected (k : Nat) :
    StronglyConnected (fun u v : Fin (k + 1) ↦ 0 < edge (k + 1) u v) := by
  have fromZero : ∀ v : Fin (k + 1),
      Relation.ReflTransGen (fun u v ↦ 0 < edge (k + 1) u v) 0 v := by
    intro v
    induction v using Fin.induction with
    | zero => exact .refl
    | succ i ih =>
        exact ih.tail (by simp [edge])
  have toZero : ∀ v : Fin (k + 1),
      Relation.ReflTransGen (fun u v ↦ 0 < edge (k + 1) u v) v 0 := by
    intro v
    induction v using Fin.induction with
    | zero => exact .refl
    | succ i ih =>
        exact ih.head (by simp [edge])
  exact fun u v ↦ (toZero u).trans (fromZero v)

/-- Before reaching the far endpoint, the appended vertex is not adjacent. -/
theorem edge_last_zero (k : Nat) (v : Fin (k + 1)) (hv : v.val < k) :
    edge (k + 1 + 1) (Fin.last (k + 1)) v.castSucc = 0 ∧
    edge (k + 1 + 1) v.castSucc (Fin.last (k + 1)) = 0 := by
  simp only [edge, Fin.val_last, Fin.val_castSucc]
  constructor <;> split_ifs <;> omega

/-- Appending one vertex preserves the old vertices' outdegrees away from
its point of attachment. -/
theorem same_degree (k : Nat) (v : Fin (k + 1)) (hv : v.val < k) :
    (∑ u, edge (k + 1) v u) =
      ∑ u, edge (k + 1 + 1) v.castSucc u := by
  symm
  rw [Fin.sum_univ_castSucc]
  simp [edge_last_zero k v hv]

/-- Incoming multisets match whenever corresponding old neighbors match. -/
theorem same_incoming {A : Type} (k : Nat) (v : Fin (k + 1)) (hv : v.val < k)
    (left : Fin (k + 1) → A) (right : Fin (k + 1 + 1) → A)
    (equalNeighbors : ∀ u : Fin (k + 1), 0 < edge (k + 1) u v →
      left u = right u.castSucc) :
    incoming (edge (k + 1)) left v =
      incoming (edge (k + 1 + 1)) right v.castSucc := by
  classical
  unfold incoming
  symm
  rw [Fin.sum_univ_castSucc]
  rw [(edge_last_zero k v hv).1]
  simp only [Multiset.replicate_zero, add_zero, edge_castSucc]
  apply Finset.sum_congr rfl
  intro u _
  by_cases he : 0 < edge (k + 1) u v
  · rw [equalNeighbors u he]
  · have hz : edge (k + 1) u v = 0 := by omega
    simp [hz]

/-- The precise common-prefix invariant from the paper's all-leader construction. -/
theorem common_prefix (k time : Nat) (v : Fin (k + 1)) (hcone : v.val + time ≤ k) :
    history (network (k + 1)) (allLeaders k) time v =
      history (network (k + 1 + 1)) (extendedLeaders k) time v.castSucc := by
  induction time generalizing v with
  | zero => simp [history, allLeaders]
  | succ time ih =>
      have hv : v.val < k := by omega
      apply Prod.ext (ih v (by omega))
      apply Prod.ext (same_degree k v hv)
      apply same_incoming k v hv
      intro u hedge
      have hunear : u.val ≤ v.val + 1 := by
        unfold edge at hedge
        split_ifs at hedge with h
        · rcases h with h | h <;> omega
        · omega
      exact ih u (by omega)

/-- The designated endpoint histories agree through round `n-1` for `n=k+1`. -/
theorem endpoint_common_prefix (k : Nat) :
    history (network (k + 1)) (allLeaders k) k 0 =
      history (network (k + 1 + 1)) (extendedLeaders k) k 0 := by
  exact common_prefix k k 0 (by simp)

/-- Neither execution can safely make a common decision at the endpoint
by round `n-1`. In particular the smaller all-leader network cannot have
terminated by that round. The protocol may use silent halting. -/
theorem endpoint_active_at_n_sub_one {State : Type} (P : Protocol State) (k : Nat)
    (safeSmall : ∀ s m,
      P.trace (k + 1) (network (k + 1)) (allLeaders k) k 0 = .halted s m → m = k + 1)
    (safeLarge : ∀ s m,
      P.trace (k + 1) (network (k + 1 + 1)) (extendedLeaders k) k 0 = .halted s m →
      m = k + 1 + 1) :
    ∃ s, P.trace (k + 1) (network (k + 1)) (allLeaders k) k 0 = .active s := by
  apply P.common_history_prevents_halting (k + 1)
    (network (k + 1)) (network (k + 1 + 1)) (allLeaders k) (extendedLeaders k) k 0 0
    (endpoint_common_prefix k)
  · simp
  · simpa using safeSmall
  · simpa using safeLarge

@[simp] theorem small_leaderCount (k : Nat) :
    Counting.leaderCount (allLeaders k) = k + 1 := by
  simp [Counting.leaderCount, allLeaders]

@[simp] theorem large_leaderCount (k : Nat) :
    Counting.leaderCount (extendedLeaders k) = k + 1 := by
  classical
  unfold Counting.leaderCount
  rw [Finset.card_eq_sum_ones, Finset.sum_filter, Fin.sum_univ_castSucc]
  have hbound : ∀ v : Fin (k + 1), v.val ≤ k := fun v ↦ by omega
  simp [extendedLeaders, hbound]

theorem small_admissible (k : Nat) :
    Admissible (k + 1) (network (k + 1)) (allLeaders k) where
  positive := by omega
  leaders := small_leaderCount k
  connected := fun _ _ ↦ path_stronglyConnected k

theorem large_admissible (k : Nat) :
    Admissible (k + 1) (network (k + 1 + 1)) (extendedLeaders k) where
  positive := by omega
  leaders := large_leaderCount k
  connected := fun _ _ ↦ path_stronglyConnected (k + 1)

/-- Every universally correct protocol needs at least `n` rounds on an
all-leader network of order `n=k+1`. This includes `n=1`, with a loopless
zero-arc singleton and an initially indistinguishable leader in a two-vertex path. -/
theorem all_leaders_lower_bound {State : Type} (P : Protocol State)
    (correct : P.SolvesCounting) (k : Nat) :
    ∃ s, P.trace (k + 1) (network (k + 1)) (allLeaders k) k 0 = .active s := by
  apply universal_lower_bound P correct (k + 1)
    (network (k + 1)) (network (k + 1 + 1)) (allLeaders k) (extendedLeaders k)
    (small_admissible k) (large_admissible k) k 0 0
  · simp
  · exact endpoint_common_prefix k

/-- Quantitative form: any halting round of the designated endpoint is at
least the order of the smaller all-leader path. -/
theorem endpoint_halt_round_ge_order {State : Type} (P : Protocol State)
    (correct : P.SolvesCounting) (k time : Nat) (state : State) (output : Nat)
    (halted : P.trace (k + 1) (network (k + 1)) (allLeaders k) time 0 =
      .halted state output) : k + 1 ≤ time := by
  by_contra h
  have ht : time ≤ k := by omega
  obtain ⟨activeState, hactive⟩ := all_leaders_lower_bound P correct k
  have hlate := P.halted_forever (k + 1) (network (k + 1)) (allLeaders k)
    time 0 state output halted (k - time)
  have heq : time + (k - time) = k := by omega
  rw [heq, hactive] at hlate
  cases hlate

end Counting.LowerAllLeaders
