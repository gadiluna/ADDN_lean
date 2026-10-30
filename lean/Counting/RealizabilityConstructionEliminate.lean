import Counting.BalancedVertexCounts

/-! Conservation laws for the auxiliary-vertex elimination used in the
fixed-order realization construction. Incoming arcs at an auxiliary vertex
all have one old selected type. Pairing them with outgoing arcs therefore
preserves the incoming multiplicity of that type at every remaining agent.
-/

namespace Counting.RealizabilityConstruction
open Counting.BalancedVertex

variable {V C : Type*} [Fintype V]

theorem eliminate_eq_of_no_incoming (D : Option V → Option V → Nat)
    (matching : Incoming D ≃ Outgoing D) (x y : V)
    (zero : D (some x) none = 0) :
    eliminate D matching x y = D (some x) (some y) := by
  classical
  have empty : (Finset.univ.filter (fun i : Incoming D => i.1 = x ∧ (matching i).1 = y)) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    have hx := (Finset.mem_filter.mp hi).2.1
    have positive := Nat.zero_lt_of_lt i.2.isLt
    rw [hx, zero] at positive
    omega
  simp only [eliminate, empty, Finset.card_empty, Nat.add_zero]

theorem eliminate_eq_of_no_outgoing (D : Option V → Option V → Nat)
    (matching : Incoming D ≃ Outgoing D) (x y : V)
    (zero : D none (some y) = 0) :
    eliminate D matching x y = D (some x) (some y) := by
  classical
  have empty : (Finset.univ.filter (fun i : Incoming D => i.1 = x ∧ (matching i).1 = y)) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    have hy := (Finset.mem_filter.mp hi).2.2
    have positive := Nat.zero_lt_of_lt (matching i).2.isLt
    rw [hy, zero] at positive
    omega
  simp only [eliminate, empty, Finset.card_empty, Nat.add_zero]

/-- Removing one auxiliary vertex leaves every other auxiliary row and
column unchanged when there are no arcs between auxiliary vertices. -/
theorem eliminate_preserves_isolated_vertex (D : Option V → Option V → Nat)
    (matching : Incoming D ≃ Outgoing D) (z : V)
    (noIn : D (some z) none = 0) (noOut : D none (some z) = 0) :
    (∀ y, eliminate D matching z y = D (some z) (some y)) ∧
    (∀ x, eliminate D matching x z = D (some x) (some z)) :=
  ⟨fun y => eliminate_eq_of_no_incoming D matching z y noIn,
   fun x => eliminate_eq_of_no_outgoing D matching x z noOut⟩

/-- Pairing preserves the receipts of each old type separately. This is
stronger than conservation of total indegree. -/
theorem eliminate_colored_incoming [DecidableEq C]
    (D : Option V → Option V → Nat) (matching : Incoming D ≃ Outgoing D)
    (color : V → C) (hubColor : C)
    (tails : ∀ x, 0 < D (some x) none → color x = hubColor)
    (y : V) (c : C) :
    (∑ x : V, if color x = c then eliminate D matching x y else 0) =
      (∑ x : V, if color x = c then D (some x) (some y) else 0) +
      if hubColor = c then D none (some y) else 0 := by
  classical
  let extra (x : V) :=
    (Finset.univ.filter (fun i : Incoming D => i.1 = x ∧ (matching i).1 = y)).card
  have typed (x : V) : (if color x = c then extra x else 0) =
      if hubColor = c then extra x else 0 := by
    by_cases hzero : extra x = 0
    · simp [hzero]
    · have positive : 0 < extra x := Nat.pos_of_ne_zero hzero
      obtain ⟨i, hi⟩ := Finset.card_pos.mp positive
      have hx := (Finset.mem_filter.mp hi).2.1
      have hd : 0 < D (some x) none := by
        have h := Nat.zero_lt_of_lt i.2.isLt
        simpa only [hx] using h
      rw [tails x hd]
  calc
    _ = (∑ x : V, if color x = c then D (some x) (some y) else 0) +
        ∑ x : V, if color x = c then extra x else 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : color x = c <;> simp [hx, eliminate, extra]
    _ = (∑ x : V, if color x = c then D (some x) (some y) else 0) +
        if hubColor = c then D none (some y) else 0 := by
      congr 1
      simp only [typed]
      rw [Finset.sum_ite_irrel]
      by_cases h : hubColor = c
      · simpa only [h, if_true] using shortcut_column_sum D matching y
      · simp [h]

end Counting.RealizabilityConstruction
