import Counting.BalancedVertex

/-! Pairing incident arcs preserves the indegree and outdegree of every
remaining vertex, including multiplicities and newly created loops. -/

namespace Counting.BalancedVertex

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem incoming_fiber_card (D : Option V → Option V → Nat) (x : V) :
    (Finset.univ.filter (fun i : Incoming D => i.1 = x)).card = D (some x) none := by
  classical
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  change (∑ i : (Σ v : V, Fin (D (some v) none)), if i.1 = x then 1 else 0) = _
  rw [Fintype.sum_sigma]
  simp [apply_ite]

theorem outgoing_fiber_card (D : Option V → Option V → Nat) (y : V) :
    (Finset.univ.filter (fun o : Outgoing D => o.1 = y)).card = D none (some y) := by
  classical
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  change (∑ o : (Σ v : V, Fin (D none (some v))), if o.1 = y then 1 else 0) = _
  rw [Fintype.sum_sigma]
  simp [apply_ite]

theorem paired_outgoing_fiber_card (D : Option V → Option V → Nat)
    (matching : Incoming D ≃ Outgoing D) (y : V) :
    (Finset.univ.filter (fun i : Incoming D => (matching i).1 = y)).card = D none (some y) := by
  classical
  rw [← outgoing_fiber_card D y]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  exact matching.sum_comp (fun o => if o.1 = y then 1 else 0)

theorem shortcut_row_sum (D : Option V → Option V → Nat)
    (matching : Incoming D ≃ Outgoing D) (x : V) :
    (∑ y : V, (Finset.univ.filter (fun i : Incoming D => i.1 = x ∧ (matching i).1 = y)).card) =
      D (some x) none := by
  classical
  have h := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ.filter (fun i : Incoming D => i.1 = x)) Finset.univ (fun i => (matching i).1)
  simpa only [Finset.filter_filter, Finset.mem_univ,
    Finset.filter_true, and_true, incoming_fiber_card] using h

theorem shortcut_column_sum (D : Option V → Option V → Nat)
    (matching : Incoming D ≃ Outgoing D) (y : V) :
    (∑ x : V, (Finset.univ.filter (fun i : Incoming D => i.1 = x ∧ (matching i).1 = y)).card) =
      D none (some y) := by
  classical
  have h := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ.filter (fun i : Incoming D => (matching i).1 = y)) Finset.univ (fun i => i.1)
  simpa only [Finset.filter_filter, Finset.mem_univ,
    Finset.filter_true, and_comm, true_and, paired_outgoing_fiber_card] using h

/-- Every outgoing arc at a remaining vertex survives directly or is
replaced by exactly one shortcut with the same tail. -/
theorem eliminate_outdegree (D : Option V → Option V → Nat)
    (matching : Incoming D ≃ Outgoing D) (x : V) :
    (∑ y : V, eliminate D matching x y) = ∑ y : Option V, D (some x) y := by
  classical
  simp only [eliminate, Finset.sum_add_distrib, Fintype.sum_option]
  calc
    _ = (∑ y : V, D (some x) (some y)) + D (some x) none := by
      congr 1
      convert shortcut_row_sum D matching x using 1
      apply Finset.sum_congr rfl
      intro y _
      congr 1
      ext i
      simp
    _ = _ := Nat.add_comm _ _

/-- Every incoming arc at a remaining vertex survives directly or is
replaced by exactly one shortcut with the same head. -/
theorem eliminate_indegree (D : Option V → Option V → Nat)
    (matching : Incoming D ≃ Outgoing D) (y : V) :
    (∑ x : V, eliminate D matching x y) = ∑ x : Option V, D x (some y) := by
  classical
  simp only [eliminate, Finset.sum_add_distrib, Fintype.sum_option]
  calc
    _ = (∑ x : V, D (some x) (some y)) + D none (some y) := by
      congr 1
      convert shortcut_column_sum D matching y using 1
      apply Finset.sum_congr rfl
      intro x _
      congr 1
      ext i
      simp
    _ = _ := Nat.add_comm _ _

end Counting.BalancedVertex
