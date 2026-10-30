import Counting.HardnessVisibleGroups

namespace Counting.HardnessVisible
open DirectedCounting PaperHistory TimingProtocolLocal HardnessPath HardnessBaseline
open scoped BigOperators

variable {V : Type} [Fintype V]
variable (G : Nat → V → V → Nat) (leader : V → Bool)
variable {q m : Nat} (inst : X3C.Instance q m)

theorem observer_first_history (observer : V)
    (same : history G leader (X3C.base q) observer = X3CBaseline.leaderView inst) :
    history G leader 1 observer = leaderHistory inst.coefficient inst.weightedTarget 1 := by
  have earlier := congrArg (ancestor 1 (X3C.base q)) same
  have within : 1 ≤ X3C.base q := by unfold X3C.base; omega
  rw [ancestor_history G leader 1 _ within] at earlier
  unfold X3CBaseline.leaderView at earlier
  rw [ancestor_history _ _ 1 _ within] at earlier
  have prefixEq : history (X3CBaseline.graph inst) (HardnessPath.leader (X3C.baselineGroups q m)) 1 none =
      history (pathNetwork inst.coefficient (X3C.baselineGroups q m)) (HardnessPath.leader (X3C.baselineGroups q m)) 1 none :=
    prefix_history _ _ _ 1 (by unfold X3C.base; omega) none
  rw [prefixEq] at earlier
  exact earlier.trans (path_histories inst.coefficient (X3C.baselineGroups q m)
    inst.weightedTarget inst.baselineGroups_equation 1
      (fun i => lt_of_lt_of_le (by unfold X3C.base; omega) (X3CBaseline.baseline_lengths i))).1

theorem observer_leader (observer : V)
    (same : history G leader (X3C.base q) observer = X3CBaseline.leaderView inst) :
    leader observer = true :=
  congrArg Prod.fst (observer_first_history G leader inst observer same)

theorem unique_observer (network : Admissible 1 G leader) (observer : V)
    (same : history G leader (X3C.base q) observer = X3CBaseline.leaderView inst) (v : V) :
    leader v = true ↔ v = observer := by
  classical
  have counted := network.leaders
  unfold leaderCount at counted
  obtain ⟨unique, equal⟩ := Finset.card_eq_one.mp counted
  have characterization (x : V) : leader x = true ↔ x = unique := by
    have membership : x ∈ Finset.univ.filter (fun x => leader x = true) ↔ x ∈ ({unique} : Finset V) := by rw [equal]
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton] using membership
  have observed := (characterization observer).mp (observer_leader G leader inst observer same)
  simpa only [observed] using characterization v

theorem observer_degree (observer : V)
    (same : history G leader (X3C.base q) observer = X3CBaseline.leaderView inst) :
    (∑ v, G 1 observer v) = inst.weightedTarget :=
  congrArg (fun H : FullHistory 1 => H.2.1) (observer_first_history G leader inst observer same)

theorem observer_loop_zero (network : Admissible 1 G leader) (observer : V)
    (same : history G leader (X3C.base q) observer = X3CBaseline.leaderView inst) :
    G 1 observer observer = 0 := by
  classical
  have messages := congrArg (fun H : FullHistory 1 => H.2.2.count true)
    (observer_first_history G leader inst observer same)
  change (incoming (G 1) leader observer).count true = _ at messages
  rw [count_incoming] at messages
  simp only [unique_observer G leader inst network observer same, Finset.sum_ite_eq', Finset.mem_univ,
    if_true] at messages
  have absent : (true : FullHistory 0) ∉ (leaderHistory inst.coefficient inst.weightedTarget 1).2.2 := by
    change true ∉ ∑ _ : Option (Fin m), ({false} : Multiset Bool)
    simp
  rw [Multiset.count_eq_zero.mpr absent] at messages
  exact messages

/-- Every physical member of a visible group receives exactly its coefficient
from the unique leader. This is equality of arc multiplicities in the new
realization, obtained from messages rather than transferred baseline fibers. -/
theorem group_receipt (network : Admissible 1 G leader) (observer : V)
    (same : history G leader (X3C.base q) observer = X3CBaseline.leaderView inst)
    (i : Option (Fin m)) (v : V) (member : v ∈ group G leader inst i) :
    G 1 observer v = inst.coefficient i := by
  classical
  obtain ⟨p, equal⟩ := (mem_group G leader inst i v).mp member
  have messages := congrArg (fun H : FullHistory 1 => H.2.2.count true) equal
  change (incoming (G 1) leader v).count true = _ at messages
  rw [count_incoming] at messages
  simp only [unique_observer G leader inst network observer same, Finset.sum_ite_eq', Finset.mem_univ,
    if_true] at messages
  cases position : p.val with
  | zero =>
    simp only [memberHistory_succ, position, leaderHistory_zero, add_zero] at messages
    change G 1 observer v = (Multiset.replicate (inst.coefficient i) (true : Bool)).count true at messages
    simpa only [Multiset.count_replicate_self] using messages
  | succ p =>
    simp only [memberHistory_succ, position, leaderHistory_zero, memberHistory_zero] at messages
    change G 1 observer v = (Multiset.replicate (inst.coefficient i) (true : Bool) + {false}).count true at messages
    simpa only [Multiset.count_add, Multiset.count_replicate_self, Multiset.count_singleton,
      Bool.true_eq_false, if_false, Nat.add_zero] using messages

end Counting.HardnessVisible
