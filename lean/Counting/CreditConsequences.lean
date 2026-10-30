import Counting.CreditHistory

namespace Counting.CreditHistory.PrefixChecks
open DirectedCounting PaperHistory

variable {V : Type*} [Fintype V]
variable {G : Nat → V → V → Nat} {leader : V → Bool} {m h : Nat}
variable {visible : ∀ r, Finset (Node G leader r)}
variable {candidate : ∀ r, Node G leader r → Nat}
variable (C : PrefixChecks G leader m h visible candidate)

include C in
theorem candidate_leader_total (r : Nat) (hr : r ≤ h) :
    (∑ i ∈ visible r ∩ Finset.univ.filter (fun c => label G leader r c = true),
      candidate r i) = FlatHistory.leaderCount leader :=
  CoreHistory.leader_candidate_of_anchor G leader h (FlatHistory.leaderCount leader)
    visible candidate C.anchor_leader_candidate C.parent_visible C.backward r hr

include C in
theorem initial_credit_bound :
    (∑ i ∈ visible 0, credit (anonymity G leader 0 i) (candidate 0 i)) ≤ m - 1 := by
  have strict := CoreCertificate.initial_credit_lt_candidate_total
    (visible 0) (Finset.univ.filter (fun c => label G leader 0 c = true))
    (anonymity G leader 0) (candidate 0) (FlatHistory.leaderCount leader)
    (fun i _ => anonymity_pos G leader 0 i) (label_mass_eq G leader 0 true)
    (C.candidate_leader_total 0 (Nat.zero_le h)) C.leader_positive
  rw [C.candidate_total 0 (Nat.zero_le h)] at strict
  omega

end Counting.CreditHistory.PrefixChecks

namespace Counting.CoreHistory.PaperChecks
open DirectedCounting PaperHistory

variable {V : Type*} [Fintype V]
variable {G : Nat → V → V → Nat} {leader : V → Bool} {m h : Nat}
variable {visible : ∀ r, Finset (Node G leader r)}
variable {candidate : ∀ r, Node G leader r → Nat}

/-- The suffix descendant audit bounds the number of final visible classes by
anchor credit plus the number of anchor classes, using actual disjoint fibers. -/
theorem suffix_credit_bound (C : PaperChecks G leader m h visible candidate) :
    (visible m).card ≤
      (∑ i ∈ visible h, credit (anonymity G leader h i) (candidate h i)) + (visible h).card := by
  exact CoreCertificate.suffix_credit_bound (ancestor G leader h m) (visible h) (visible m)
    (anonymity G leader h) (candidate h) (anonymity G leader m)
    (ancestor_visible_of_parent_visible G leader h m C.anchor_le_final visible C.parent_visible)
    (descendants_nonempty_of_children G leader h m C.anchor_le_final visible C.children_nonempty)
    (fun i _ => anonymity_pos G leader m i)
    (fun u _ => descendants_mass_le G leader h m C.anchor_le_final (visible m) u) C.suffix_audit

end Counting.CoreHistory.PaperChecks
