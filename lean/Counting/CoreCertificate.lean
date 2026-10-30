import Counting.CreditLoss

/-!
# Soundness of the core counting certificate

This file formalizes the contradiction used to reject a false candidate in
Theorem `thm:one-leader`. The interface contains finite-level data and the
structural, arithmetic and suffix checks. It never assumes credit loss or
false-candidate rejection. Those conclusions are derived below.

CoreHistory and the executable refinement modules connect `AuditedCorePrefix`
to vistas and the five-step test. Flatness of the anchor and uniqueness of the
linear solution are needed for acceptance of the true candidate, but not
for the soundness result proved here; the interface records only the
conditions needed for this soundness argument.
-/

namespace Counting.CoreCertificate

/-- A branching transition with a child for every old node strictly
increases the number of visible nodes. -/
theorem card_lt_of_nonflat {Old New : Type*} [DecidableEq Old]
    (parent : New → Old) (old : Finset Old) (next : Finset New)
    (maps : ∀ i ∈ next, parent i ∈ old)
    (children : ∀ u ∈ old, (next.filter (fun i => parent i = u)).Nonempty)
    (nonflat : ¬ ∀ u ∈ old, (next.filter (fun i => parent i = u)).card = 1) :
    old.card < next.card := by
  classical
  have hcount : next.card = ∑ u ∈ old, (next.filter (fun i => parent i = u)).card :=
    Finset.card_eq_sum_card_fiberwise maps
  have hle : ∀ u ∈ old, 1 ≤ (next.filter (fun i => parent i = u)).card := by
    intro u hu
    exact Finset.card_pos.mpr (children u hu)
  push Not at nonflat
  obtain ⟨u, hu, hnotone⟩ := nonflat
  have hstrict := Finset.sum_lt_sum hle ⟨u, hu, by have := hle u hu; omega⟩
  simpa only [Finset.sum_const, smul_eq_mul, mul_one, ← hcount] using hstrict

/-- The suffix test bounds the number of descendant fibers by candidate
anonymity. Disjoint positive actual fibers give the other bound. -/
theorem suffix_credit_bound {Anchor Last : Type*} [DecidableEq Anchor]
    (ancestor : Last → Anchor) (anchor : Finset Anchor) (last : Finset Last)
    (actual candidate : Anchor → ℕ) (lastActual : Last → ℕ)
    (maps : ∀ i ∈ last, ancestor i ∈ anchor)
    (nonempty : ∀ u ∈ anchor, (last.filter (fun i => ancestor i = u)).Nonempty)
    (positive : ∀ i ∈ last, 0 < lastActual i)
    (refinement : ∀ u ∈ anchor,
      (∑ i ∈ last.filter (fun i => ancestor i = u), lastActual i) ≤ actual u)
    (audit : ∀ u ∈ anchor, (last.filter (fun i => ancestor i = u)).card ≤ candidate u) :
    last.card ≤ (∑ u ∈ anchor, credit (actual u) (candidate u)) + anchor.card := by
  have perNode : ∀ u ∈ anchor,
      (last.filter (fun i => ancestor i = u)).card ≤ credit (actual u) (candidate u) + 1 := by
    intro u hu
    have ha : (last.filter (fun i => ancestor i = u)).card ≤ actual u := by
      calc
        (last.filter (fun i => ancestor i = u)).card =
            ∑ _ ∈ last.filter (fun i => ancestor i = u), 1 := by simp
        _ ≤ ∑ i ∈ last.filter (fun i => ancestor i = u), lastActual i :=
          Finset.sum_le_sum fun i hi => positive i (Finset.mem_filter.mp hi).1
        _ ≤ actual u := refinement u hu
    have hb := audit u hu
    have hq := Finset.card_pos.mpr (nonempty u hu)
    unfold credit
    omega
  calc
    last.card = ∑ u ∈ anchor, (last.filter (fun i => ancestor i = u)).card :=
      Finset.card_eq_sum_card_fiberwise maps
    _ ≤ ∑ u ∈ anchor, (credit (actual u) (candidate u) + 1) := Finset.sum_le_sum perNode
    _ = (∑ u ∈ anchor, credit (actual u) (candidate u)) + anchor.card := by
      simp [Finset.sum_add_distrib]

/-- Leader normalization leaves at least one candidate unit uncredited. -/
theorem initial_credit_lt_candidate_total {Node : Type*} [DecidableEq Node]
    (visible leaders : Finset Node) (actual candidate : Node → ℕ) (ell : ℕ)
    (positive : ∀ i ∈ visible, 0 < actual i)
    (actualLeaders : ∑ i ∈ leaders, actual i = ell)
    (candidateLeaders : ∑ i ∈ visible ∩ leaders, candidate i = ell) (hell : 0 < ell) :
    (∑ i ∈ visible, credit (actual i) (candidate i)) < ∑ i ∈ visible, candidate i := by
  have hne : (visible ∩ leaders).Nonempty := by
    by_contra h
    have he : visible ∩ leaders = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp only [he, Finset.sum_empty] at candidateLeaders
    omega
  have hle : (∑ i ∈ visible ∩ leaders, actual i) ≤ ∑ i ∈ visible ∩ leaders, candidate i := by
    rw [candidateLeaders, ← actualLeaders]
    exact Finset.sum_le_sum_of_subset Finset.inter_subset_right
  obtain ⟨j, hj, hjle⟩ := exists_actual_le_candidate _ actual candidate hne hle
  have hjvisible := (Finset.mem_inter.mp hj).1
  apply Finset.sum_lt_sum (fun i _ => credit_le_candidate (actual i) (candidate i))
  refine ⟨j, hjvisible, ?_⟩
  have := credit_add_one_le_actual (candidate := candidate j) (positive j hjvisible)
  omega

/-- Finite varying levels and the actual hypotheses checked or justified
for a passed core-algorithm test. Candidate totals before the anchor are
derived from backward propagation below, rather than assumed. -/
structure AuditedCorePrefix (Node : ℕ → Type*) [∀ r, Fintype (Node r)]
    [∀ r, DecidableEq (Node r)] (m h n ell : ℕ) where
  anchor_positive : 1 ≤ h
  anchor_le_final : h ≤ m
  leader_positive : 0 < ell
  visible : ∀ r, Finset (Node r)
  leaders : ∀ r, Finset (Node r)
  parent : ∀ r, Node (r + 1) → Node r
  actual : ∀ r, Node r → ℕ
  candidate : ∀ r, Node r → ℕ
  degree : ∀ r, Node (r + 1) → ℕ
  weight : ∀ r, Node r → Node (r + 1) → ℕ
  actual_positive : ∀ r, r ≤ m → ∀ i, 0 < actual r i
  candidate_positive : ∀ r, r ≤ h → ∀ i ∈ visible r, 0 < candidate r i
  population : ∀ r, r ≤ m → (∑ i, actual r i) = n
  leader_actual : ∀ r, r ≤ h → (∑ i ∈ leaders r, actual r i) = ell
  leader_candidate : ∀ r, r ≤ h → (∑ i ∈ visible r ∩ leaders r, candidate r i) = ell
  parent_visible : ∀ r, r < m → ∀ i ∈ visible (r + 1), parent r i ∈ visible r
  children_nonempty : ∀ r, r < m → ∀ u ∈ visible r,
    ((visible (r + 1)).filter (fun i => parent r i = u)).Nonempty
  partition : ∀ r, r < h → ∀ u,
    (∑ i ∈ Finset.univ.filter (fun i => parent r i = u), actual (r + 1) i) = actual r u
  backward : ∀ r, r < h → ∀ u ∈ visible r,
    (∑ i ∈ (visible (r + 1)).filter (fun i => parent r i = u), candidate (r + 1) i) = candidate r u
  actual_flow : ∀ r, r < h → ∀ u,
    (∑ i, if parent r i = u then degree r i * actual (r + 1) i else 0) =
    ∑ i, weight r u i * actual (r + 1) i
  candidate_flow : ∀ r, r < h → ∀ u ∈ visible r,
    (∑ i ∈ visible (r + 1), if parent r i = u then degree r i * candidate (r + 1) i else 0) =
    ∑ i ∈ visible (r + 1), weight r u i * candidate (r + 1) i
  connected : ∀ r, r < h → ∀ i j,
    Relation.ReflTransGen (fun p q => 0 < weight r (parent r p) q) i j
  anchor_total : (∑ i ∈ visible h, candidate h i) = m
  suffix_nonflat : ∀ r, h ≤ r → r < m →
    ¬ ∀ u ∈ visible r, ((visible (r + 1)).filter (fun i => parent r i = u)).card = 1
  ancestor : Node m → Node h
  ancestor_visible : ∀ i ∈ visible m, ancestor i ∈ visible h
  descendants_nonempty : ∀ u ∈ visible h, ((visible m).filter (fun i => ancestor i = u)).Nonempty
  descendants_mass : ∀ u ∈ visible h,
    (∑ i ∈ (visible m).filter (fun i => ancestor i = u), actual m i) ≤ actual h u
  suffix_audit : ∀ u ∈ visible h,
    ((visible m).filter (fun i => ancestor i = u)).card ≤ candidate h u

namespace AuditedCorePrefix

variable {Node : ℕ → Type*} [∀ r, Fintype (Node r)] [∀ r, DecidableEq (Node r)]
  {m h n ell : ℕ} (C : AuditedCorePrefix Node m h n ell)

def potential (r : ℕ) : ℕ := ∑ i ∈ C.visible r, credit (C.actual r i) (C.candidate r i)

theorem candidate_total (r : ℕ) (hr : r ≤ h) :
    (∑ i ∈ C.visible r, C.candidate r i) = m := by
  have hp : ∀ t, t ≤ h → (∑ i ∈ C.visible t, C.candidate t i) =
      ∑ i ∈ C.visible 0, C.candidate 0 i := by
    intro t
    induction t with
    | zero => intro _; rfl
    | succ t ih =>
      intro ht
      have htlt : t < h := by omega
      have htm : t < m := lt_of_lt_of_le htlt C.anchor_le_final
      calc
        (∑ i ∈ C.visible (t + 1), C.candidate (t + 1) i) =
            ∑ u ∈ C.visible t, ∑ i ∈ (C.visible (t + 1)).filter (fun i => C.parent t i = u),
              C.candidate (t + 1) i := (Finset.sum_fiberwise_of_maps_to (C.parent_visible t htm) _).symm
        _ = ∑ u ∈ C.visible t, C.candidate t u :=
          Finset.sum_congr rfl (C.backward t htlt)
        _ = ∑ i ∈ C.visible 0, C.candidate 0 i := ih (by omega)
  exact (hp r hr).trans ((hp h le_rfl).symm.trans C.anchor_total)

theorem potential_mono (r : ℕ) (hr : r < h) : C.potential (r + 1) ≤ C.potential r := by
  have hrm : r < m := lt_of_lt_of_le hr C.anchor_le_final
  have hr1m : r + 1 ≤ m := by omega
  have hbound : ∀ u, (∑ i ∈ (C.visible (r + 1)).filter (fun i => C.parent r i = u),
      C.actual (r + 1) i) ≤ C.actual r u := by
    intro u
    rw [← C.partition r hr u]
    apply Finset.sum_le_sum_of_subset
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, (Finset.mem_filter.mp hi).2⟩
  calc
    C.potential (r + 1) = ∑ u ∈ C.visible r,
        ∑ i ∈ (C.visible (r + 1)).filter (fun i => C.parent r i = u),
          credit (C.actual (r + 1) i) (C.candidate (r + 1) i) :=
      (Finset.sum_fiberwise_of_maps_to (C.parent_visible r hrm) _).symm
    _ ≤ C.potential r := Finset.sum_le_sum fun u hu =>
      credit_under_refinement _ (C.actual (r + 1)) (C.candidate (r + 1)) _ _
        (C.children_nonempty r hrm u hu) (fun i _ => C.actual_positive (r + 1) hr1m i)
        (hbound u) (C.backward r hr u hu)

theorem potential_eq_identifies_population (r : ℕ) (hr : r < h)
    (heq : C.potential (r + 1) = C.potential r) : m = n := by
  have hrm : r < m := lt_of_lt_of_le hr C.anchor_le_final
  have hr1m : r + 1 ≤ m := by omega
  have hr1h : r + 1 ≤ h := by omega
  obtain ⟨hfull, hvalues⟩ := credit_preserved_identifies_population
    (C.parent r) (C.visible (r + 1)) (C.visible r) (C.actual (r + 1)) (C.candidate (r + 1))
    (C.degree r) (C.weight r) (C.actual r) (C.candidate r) (C.leaders (r + 1)) ell
    (C.actual_positive (r + 1) hr1m) (C.candidate_positive (r + 1) hr1h)
    (C.parent_visible r hrm) (C.children_nonempty r hrm)
    (C.partition r hr) (C.backward r hr) (C.actual_flow r hr) (C.candidate_flow r hr)
    (C.connected r hr) (C.leader_actual (r + 1) hr1h) (C.leader_candidate (r + 1) hr1h)
    C.leader_positive heq
  calc
    m = ∑ i ∈ C.visible (r + 1), C.candidate (r + 1) i := (C.candidate_total (r + 1) hr1h).symm
    _ = ∑ i, C.actual (r + 1) i := by rw [hfull, ← hvalues]
    _ = n := C.population (r + 1) hr1m

theorem initial_credit_bound : C.potential 0 < m := by
  have := initial_credit_lt_candidate_total (C.visible 0) (C.leaders 0) (C.actual 0) (C.candidate 0) ell
    (fun i _ => C.actual_positive 0 (Nat.zero_le m) i)
    (C.leader_actual 0 (Nat.zero_le h)) (C.leader_candidate 0 (Nat.zero_le h)) C.leader_positive
  rwa [C.candidate_total 0 (Nat.zero_le h)] at this

theorem suffix_credit_bound : (C.visible m).card ≤ C.potential h + (C.visible h).card :=
  CoreCertificate.suffix_credit_bound C.ancestor (C.visible h) (C.visible m)
    (C.actual h) (C.candidate h) (C.actual m) C.ancestor_visible C.descendants_nonempty
    (fun i _ => C.actual_positive m le_rfl i) C.descendants_mass C.suffix_audit

theorem suffix_growth : (C.visible h).card + (m - h) ≤ (C.visible m).card := by
  have hgrowth : ∀ k, h + k ≤ m → (C.visible h).card + k ≤ (C.visible (h + k)).card := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have hprev := ih (by omega)
      have hstrict := card_lt_of_nonflat (C.parent (h + k)) (C.visible (h + k))
        (C.visible (h + k + 1)) (C.parent_visible (h + k) (by omega))
        (C.children_nonempty (h + k) (by omega))
        (C.suffix_nonflat (h + k) (by omega) (by omega))
      have heq : h + (k + 1) = h + k + 1 := by omega
      rw [heq]
      omega
  have hhm : h + (m - h) = m := Nat.add_sub_of_le C.anchor_le_final
  have hresult := hgrowth (m - h) (by omega)
  rwa [hhm] at hresult

include C in
/-- Soundness of the core five-step certificate. All credit inequalities
are derived above from its individual structural and arithmetic checks. -/
theorem accepted_candidate_eq_population : m = n := by
  by_contra hfalse
  have hstrict : ∀ r, r < h → C.potential (r + 1) < C.potential r := by
    intro r hr
    have hle := C.potential_mono r hr
    have hne : C.potential (r + 1) ≠ C.potential r := fun heq =>
      hfalse (C.potential_eq_identifies_population r hr heq)
    exact lt_of_le_of_ne hle hne
  have hdrop : ∀ r, r ≤ h → C.potential r + r ≤ C.potential 0 := by
    intro r
    induction r with
    | zero => intro _; omega
    | succ r ih =>
      intro hr
      have hprior := ih (by omega)
      have hnext := hstrict r (by omega)
      omega
  have hupper := hdrop h le_rfl
  have hinitial := C.initial_credit_bound
  have hlower := C.suffix_credit_bound
  have hgrowth := C.suffix_growth
  have hanchor := C.anchor_le_final
  omega

end AuditedCorePrefix
end Counting.CoreCertificate
