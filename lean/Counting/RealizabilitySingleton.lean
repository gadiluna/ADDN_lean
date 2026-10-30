import Counting.RealizabilityAllocation
import Counting.VistaIsomorphism

/-!
# Realizing a fixed-order certificate at order one

Positivity and the population bound force one visible node, of count one,
at every level. Full balance then determines exactly the singleton's loop
multiplicity. This includes depth zero and rounds with no arcs.
-/

namespace Counting.Realizability
open DirectedCounting TimingProtocolLocal VistaIsomorphism

theorem blackAncestor_mem_occurrences (r d : Nat) (H : FullHistory (r + d)) :
    blackAncestor r d H ∈ occurrences r d H := by
  induction d with
  | zero => exact Finset.mem_singleton_self H
  | succ d ih => exact Finset.mem_union_left _ (ih H.1)

theorem ancestor_mem_levels (r t : Nat) (H : FullHistory t) (within : r ≤ t) :
    ancestor r t H ∈ levels t H r := by
  unfold ancestor levels
  rw [dif_pos within, dif_pos within]
  exact blackAncestor_mem_occurrences r (t - r) _

theorem ancestor_self (t : Nat) (H : FullHistory t) : ancestor t t H = H := by
  have h := ancestor_mem_levels t t H le_rfl
  rw [levels_top] at h
  exact Finset.mem_singleton.mp h

variable {ell t : Nat} {H : FullHistory t} {k : Counts}

theorem Certificate.singleton_leaders (cert : Certificate ell 1 t H k) : ell = 1 := by
  have := cert.leaders_positive
  have := cert.order_ge_leaders
  omega

theorem Certificate.singleton_count (cert : Certificate ell 1 t H k) (r : Nat)
    (within : r ≤ t) (v : FullHistory r) (visible : v ∈ levels t H r) : k r v = 1 := by
  have lower := cert.positive r within v visible
  have upper := cert.count_le_order r ⟨v, visible⟩
  change k r v ≤ 1 at upper
  omega

/-- Every visible level is precisely the observer's black ancestor. -/
theorem Certificate.singleton_level (cert : Certificate ell 1 t H k) (r : Nat) (within : r ≤ t) :
    levels t H r = {ancestor r t H} := by
  classical
  have cardinal : (levels t H r).card ≤ 1 := by
    calc
      (levels t H r).card = ∑ v ∈ levels t H r, k r v := by
        rw [Finset.card_eq_sum_ones]
        exact Finset.sum_congr rfl (fun v hv => (cert.singleton_count r within v hv).symm)
      _ ≤ 1 := cert.selected_total_le r
  have member := ancestor_mem_levels r t H within
  ext v
  constructor
  · intro hv
    exact Finset.mem_singleton.mpr ((Finset.card_le_one.mp cardinal) v hv (ancestor r t H) member)
  · intro hv
    simpa only [Finset.mem_singleton.mp hv] using member

theorem Certificate.singleton_parent (cert : Certificate ell 1 t H k) (r : Nat) (before : r < t) :
    parent r (ancestor (r + 1) t H) = ancestor r t H := by
  have visible := cert.parent_visible r before _ (ancestor_mem_levels (r + 1) t H (by omega))
  rw [cert.singleton_level r (by omega)] at visible
  exact Finset.mem_singleton.mp visible

theorem Certificate.singleton_hidden (cert : Certificate ell 1 t H k) (r : Nat) (before : r < t) :
    hidden 1 (levels t H) k r = 0 := by
  unfold hidden
  rw [cert.singleton_level (r + 1) (by omega)]
  simp only [Finset.sum_singleton,
    cert.singleton_count (r + 1) (by omega) _ (ancestor_mem_levels (r + 1) t H (by omega)), Nat.sub_self]

theorem Certificate.singleton_degree_count (cert : Certificate ell 1 t H k) (r : Nat) (before : r < t) :
    degree r (ancestor (r + 1) t H) = red r (ancestor r t H) (ancestor (r + 1) t H) := by
  have nextCount := cert.singleton_count (r + 1) (by omega) _ (ancestor_mem_levels (r + 1) t H (by omega))
  have h := cert.balance_full r before (cert.singleton_hidden r before)
    (ancestor r t H) (ancestor_mem_levels r t H (by omega))
  simpa only [supply, demand, children, cert.singleton_level (r + 1) (by omega),
    Finset.filter_singleton, cert.singleton_parent r before, if_true,
    Finset.sum_singleton, nextCount, Nat.one_mul] using h

theorem Certificate.singleton_messages (cert : Certificate ell 1 t H k) (r : Nat) (before : r < t) :
    (ancestor (r + 1) t H).2.2 =
      Multiset.replicate (degree r (ancestor (r + 1) t H)) (ancestor r t H) := by
  classical
  apply Multiset.ext.mpr
  intro u
  by_cases hu : u = ancestor r t H
  · subst u
    rw [Multiset.count_replicate_self]
    exact (cert.singleton_degree_count r before).symm
  · have absent : u ∉ (ancestor (r + 1) t H).2.2 := by
      intro received
      have visible := message_mem_levels t H r (ancestor (r + 1) t H)
        (ancestor_mem_levels (r + 1) t H (by omega)) u received
      rw [cert.singleton_level r (by omega), Finset.mem_singleton] at visible
      exact hu visible
    rw [Multiset.count_eq_zero_of_notMem absent, Multiset.count_replicate, if_neg (Ne.symm hu)]

theorem Certificate.singleton_input (cert : Certificate ell 1 t H k) : ancestor 0 t H = true := by
  have visible := ancestor_mem_levels 0 t H (Nat.zero_le _)
  cases hv : ancestor 0 t H with
  | true => rfl
  | false =>
      have positive := cert.positive 0 (Nat.zero_le _) false (hv ▸ visible)
      have bound := cert.initial_nonleaders
      rw [cert.singleton_leaders] at bound
      change (if (false : FullHistory 0) ∈ levels t H 0 then k 0 false else 0) ≤ 1 - 1 at bound
      rw [if_pos (hv ▸ visible)] at bound
      omega

/-- Communication is confined to the unique vertex; an arbitrary natural
loop multiplicity is allowed, including zero. -/
def singletonNetwork (t : Nat) (H : FullHistory t) : Nat → Unit → Unit → Nat
  | 0, _, _ => 0
  | r + 1, _, _ => degree r (ancestor (r + 1) t H)

theorem Certificate.singleton_histories (cert : Certificate ell 1 t H k) :
    ∀ r, r ≤ t → history (singletonNetwork t H) (fun _ => true) r () = ancestor r t H := by
  intro r
  induction r with
  | zero => intro _; exact cert.singleton_input.symm
  | succ r ih =>
      intro within
      have before : r < t := by omega
      have previous := ih (by omega)
      change (history (singletonNetwork t H) (fun _ => true) r (),
        ∑ b : Unit, singletonNetwork t H (r + 1) () b,
        incoming (singletonNetwork t H (r + 1)) (history (singletonNetwork t H) (fun _ => true) r) ()) =
          ancestor (r + 1) t H
      apply Prod.ext (previous.trans (cert.singleton_parent r before).symm)
      apply Prod.ext
      · change (∑ _b : Unit, degree r (ancestor (r + 1) t H)) = degree r (ancestor (r + 1) t H)
        simp
      · rw [cert.singleton_messages r before]
        simp only [incoming, Fintype.sum_unique]
        exact congrArg (Multiset.replicate (degree r (ancestor (r + 1) t H))) previous

/-- Order-one sufficiency, including t=0 and zero-loop rounds. -/
theorem Certificate.singleton_realization (cert : Certificate ell 1 t H k) :
    ∃ G : Nat → Unit → Unit → Nat,
      Admissible ell G (fun _ => true) ∧ history G (fun _ => true) t () = H := by
  refine ⟨singletonNetwork t H, ?_, ?_⟩
  · constructor
    · exact cert.leaders_positive
    · rw [cert.singleton_leaders]
      simp [leaderCount]
    · intro _ _ a b
      have eq : a = b := Subsingleton.elim _ _
      subst b
      exact Relation.ReflTransGen.refl
  · exact (cert.singleton_histories t le_rfl).trans (ancestor_self t H)

end Counting.Realizability
