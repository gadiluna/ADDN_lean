import Counting.LowerAllLeaders

/-! The one-leader lower bound uses a bidirected path with a self-loop at
its nonleader endpoint. The loop delays detection of the longer path until
the leader's influence reaches the endpoint and returns. -/

namespace Counting.LowerOneLeader

open DirectedCounting
open scoped BigOperators

/-- Order is `k+2`, so the leader and the looped endpoint are distinct. -/
def edge (k : Nat) (u v : Fin (k + 2)) : Nat :=
  (if u.val + 1 = v.val then 1 else 0) +
  (if v.val + 1 = u.val then 1 else 0) +
  (if u.val = k + 1 ∧ v.val = k + 1 then 1 else 0)

def network (k : Nat) : Nat → Fin (k + 2) → Fin (k + 2) → Nat := fun _ ↦ edge k

def leader (k : Nat) (v : Fin (k + 2)) : Bool := decide (v.val = 0)

def previous (k : Nat) (v : Fin (k + 2)) : Fin (k + 2) :=
  ⟨v.val - 1, by omega⟩

def next (k : Nat) (v : Fin (k + 2)) : Fin (k + 2) :=
  ⟨min (v.val + 1) (k + 1), by omega⟩

theorem edge_symm (k : Nat) (u v : Fin (k + 2)) : edge k u v = edge k v u := by
  simp [edge, and_comm, Nat.add_comm]

theorem edge_leader (k : Nat) (u : Fin (k + 2)) :
    edge k 0 u = if u = 1 then 1 else 0 := by
  simp only [edge, Fin.val_zero, Nat.zero_add, Fin.ext_iff, Fin.val_one]
  split_ifs <;> first | omega | tauto

theorem edge_nonleader (k : Nat) (v u : Fin (k + 2)) (hv : 0 < v.val) :
    edge k v u = (if u = previous k v then 1 else 0) +
      (if u = next k v then 1 else 0) := by
  simp only [edge, previous, next, Fin.ext_iff]
  split_ifs <;> omega

theorem degree_leader (k : Nat) : (∑ u, edge k 0 u) = 1 := by
  simp [edge_leader]

theorem degree_nonleader (k : Nat) (v : Fin (k + 2)) (hv : 0 < v.val) :
    (∑ u, edge k v u) = 2 := by
  simp [edge_nonleader k v _ hv, Finset.sum_add_distrib]

theorem incoming_leader {A : Type} (k : Nat) (state : Fin (k + 2) → A) :
    incoming (edge k) state 0 = {state 1} := by
  classical
  unfold incoming
  calc
    _ = ∑ u : Fin (k + 2), if u = 1 then ({state u} : Multiset A) else 0 := by
      apply Finset.sum_congr rfl
      intro u _
      rw [edge_symm k u 0, edge_leader]
      split_ifs <;> simp
    _ = {state 1} := by simp

theorem incoming_nonleader {A : Type} (k : Nat) (state : Fin (k + 2) → A)
    (v : Fin (k + 2)) (hv : 0 < v.val) :
    incoming (edge k) state v = {state (previous k v)} + {state (next k v)} := by
  classical
  unfold incoming
  calc
    _ = ∑ u : Fin (k + 2),
        ((if u = previous k v then ({state u} : Multiset A) else 0) +
         (if u = next k v then ({state u} : Multiset A) else 0)) := by
      apply Finset.sum_congr rfl
      intro u _
      rw [edge_symm k u v, edge_nonleader k v u hv]
      split_ifs <;> simp
    _ = _ := by rw [Finset.sum_add_distrib]; simp

/-- The self-loop does not destroy connectivity of the underlying bidirected path. -/
theorem stronglyConnected (k : Nat) :
    StronglyConnected (fun u v ↦ 0 < edge k u v) := by
  intro u v
  have path := LowerAllLeaders.path_stronglyConnected (k + 1) u v
  apply Relation.ReflTransGen.mono (r := fun u v ↦ 0 < LowerAllLeaders.edge (k + 2) u v)
      (fun a b h ↦ ?_) u v path
  have adj : a.val + 1 = b.val ∨ b.val + 1 = a.val := by
    by_contra hnone
    simp [LowerAllLeaders.edge, hnone] at h
  rcases adj with hadj | hadj
  · unfold edge
    rw [if_pos hadj]
    omega
  · unfold edge
    rw [if_pos hadj]
    omega

/-- Histories of agents still beyond the leader's influence. -/
def ordinaryHistory : (time : Nat) → FullHistory time
  | 0 => false
  | time + 1 => (ordinaryHistory time, 2, {ordinaryHistory time} + {ordinaryHistory time})

theorem ordinary_history (k time : Nat) (v : Fin (k + 2)) (hfar : time < v.val) :
    history (network k) (leader k) time v = ordinaryHistory time := by
  induction time generalizing v with
  | zero =>
      simp only [history, leader, ordinaryHistory]
      simp [show v.val ≠ 0 by omega]
  | succ time ih =>
      have hv : 0 < v.val := by omega
      change (_, _, _) = (_, _, _)
      apply Prod.ext (ih v (by omega))
      apply Prod.ext (degree_nonleader k v hv)
      change incoming (edge k) _ v = _
      rw [incoming_nonleader k _ v hv]
      rw [ih (previous k v) (by dsimp [previous]; omega),
        ih (next k v) (by dsimp [next]; omega)]

@[simp] theorem previous_castSucc (k : Nat) (v : Fin (k + 2)) :
    previous (k + 1) v.castSucc = (previous k v).castSucc := rfl

theorem next_castSucc (k : Nat) (v : Fin (k + 2)) (hv : v.val < k + 1) :
    next (k + 1) v.castSucc = (next k v).castSucc := by
  apply Fin.ext
  simp only [next, Fin.val_castSucc]
  omega

@[simp] theorem leader_castSucc (k : Nat) (v : Fin (k + 2)) :
    leader (k + 1) v.castSucc = leader k v := rfl

/-- Exact invariant: information from the exceptional endpoint cannot return
to position `v` before round `2(k+2)-1-v`. -/
theorem common_prefix (k time : Nat) (v : Fin (k + 2))
    (hcone : v.val + time ≤ 2 * (k + 1)) :
    history (network k) (leader k) time v =
      history (network (k + 1)) (leader (k + 1)) time v.castSucc := by
  induction time generalizing v with
  | zero => rfl
  | succ time ih =>
      apply Prod.ext (ih v (by omega))
      have hdegree : (∑ u, edge k v u) = ∑ u, edge (k + 1) v.castSucc u := by
        by_cases hz : v = 0
        · subst v
          rw [degree_leader, show (0 : Fin (k + 2)).castSucc = 0 from rfl, degree_leader]
        · have hv : 0 < v.val := by
            have hval : v.val ≠ 0 := fun h ↦ hz (Fin.ext h)
            omega
          rw [degree_nonleader k v hv, degree_nonleader (k + 1) v.castSucc hv]
      apply Prod.ext hdegree
      by_cases hz : v = 0
      · subst v
        change incoming (edge k) _ 0 = incoming (edge (k + 1)) _ 0
        rw [incoming_leader, incoming_leader]
        have hone := ih (1 : Fin (k + 2)) (by simp only [Fin.val_one]; omega)
        exact congrArg (fun h ↦ ({h} : Multiset (FullHistory time))) hone
      · have hv : 0 < v.val := by
          have hval : v.val ≠ 0 := fun h ↦ hz (Fin.ext h)
          omega
        change incoming (edge k) _ v = incoming (edge (k + 1)) _ v.castSucc
        rw [incoming_nonleader k _ v hv, incoming_nonleader (k + 1) _ v.castSucc hv]
        rw [previous_castSucc]
        have hprevious := ih (previous k v) (by dsimp [previous]; omega)
        rw [hprevious]
        by_cases hlast : v.val = k + 1
        · have htime : time < v.val := by omega
          have hnextSmall : next k v = v := by
            apply Fin.ext
            simp [next, hlast]
          rw [hnextSmall, ordinary_history k time v htime,
            ordinary_history (k + 1) time (next (k + 1) v.castSucc)
              (by dsimp [next]; omega)]
        · have hbefore : v.val < k + 1 := by omega
          rw [next_castSucc k v hbefore]
          have hnext := ih (next k v) (by dsimp [next]; omega)
          rw [hnext]

/-- The designated leader cannot distinguish orders `n=k+2` and `n+1`
through round `2n-2`. -/
theorem endpoint_common_prefix (k : Nat) :
    history (network k) (leader k) (2 * (k + 1)) 0 =
      history (network (k + 1)) (leader (k + 1)) (2 * (k + 1)) 0 := by
  exact common_prefix k (2 * (k + 1)) 0 (by simp)

@[simp] theorem one_leader (k : Nat) : Counting.leaderCount (leader k) = 1 := by
  unfold Counting.leaderCount
  have hset : Finset.univ.filter (fun v : Fin (k + 2) ↦ leader k v = true) = {0} := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, leader,
      decide_eq_true_eq, Finset.mem_singleton, Fin.ext_iff, Fin.val_zero]
  rw [hset]
  simp

theorem admissible (k : Nat) : Admissible 1 (network k) (leader k) where
  positive := by omega
  leaders := one_leader k
  connected := fun _ _ ↦ stronglyConnected k

/-- The one-leader branch of the exact termination lower bound. -/
theorem one_leader_lower_bound {State : Type} (P : Protocol State)
    (correct : P.SolvesCounting) (k : Nat) :
    ∃ s, P.trace 1 (network k) (leader k) (2 * (k + 1)) 0 = .active s := by
  apply universal_lower_bound P correct 1 (network k) (network (k + 1))
    (leader k) (leader (k + 1)) (admissible k) (admissible (k + 1))
    (2 * (k + 1)) 0 0
  · simp
  · exact endpoint_common_prefix k

/-- Any halting round of the leader in the order-`n=k+2` looped path is
at least `2n-1`. -/
theorem endpoint_halt_round_ge_two_mul_sub_one {State : Type} (P : Protocol State)
    (correct : P.SolvesCounting) (k time : Nat) (state : State) (output : Nat)
    (halted : P.trace 1 (network k) (leader k) time 0 = .halted state output) :
    2 * (k + 2) - 1 ≤ time := by
  by_contra h
  have ht : time ≤ 2 * (k + 1) := by omega
  obtain ⟨activeState, hactive⟩ := one_leader_lower_bound P correct k
  have hlate := P.halted_forever 1 (network k) (leader k)
    time 0 state output halted (2 * (k + 1) - time)
  have heq : time + (2 * (k + 1) - time) = 2 * (k + 1) := by omega
  rw [heq, hactive] at hlate
  cases hlate

end Counting.LowerOneLeader
