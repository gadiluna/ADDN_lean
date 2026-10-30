import DirectedCountingFormalization.Connectivity
import Mathlib.Tactic

set_option warningAsError true

namespace DirectedCounting

def reachStepBool {m : Nat} (r : Fin m -> Fin m -> Bool)
    (S : Finset (Fin m)) : Finset (Fin m) :=
  S ∪ Finset.univ.filter (fun v =>
    ∃ u, u ∈ S ∧ r u v = true)

theorem mem_reachStepBool_iff {m : Nat}
    (r : Fin m → Fin m → Bool) (S : Finset (Fin m)) (v : Fin m) :
    v ∈ reachStepBool r S ↔
      v ∈ S ∨ ∃ u, u ∈ S ∧ r u v = true := by
  simp [reachStepBool]

theorem subset_reachStepBool {m : Nat}
    (r : Fin m → Fin m → Bool) (S : Finset (Fin m)) :
    S ⊆ reachStepBool r S := by
  intro v hv
  exact (mem_reachStepBool_iff r S v).2 (Or.inl hv)

def reachableFinset {m : Nat} (r : Fin m → Fin m → Bool)
    (source : Fin m) : Nat → Finset (Fin m)
  | 0 => {source}
  | k + 1 => reachStepBool r (reachableFinset r source k)

theorem reachableFinset_subset_succ {m : Nat}
    (r : Fin m → Fin m → Bool) (source : Fin m) (k : Nat) :
    reachableFinset r source k ⊆ reachableFinset r source (k + 1) := by
  simpa only [reachableFinset] using
    subset_reachStepBool r (reachableFinset r source k)

theorem reachableFinset_mono {m : Nat}
    (r : Fin m → Fin m → Bool) (source : Fin m)
    {k l : Nat} (hkl : k ≤ l) :
    reachableFinset r source k ⊆ reachableFinset r source l := by
  induction hkl with
  | refl => exact fun _ hx => hx
  | @step l hkl ih =>
      exact ih.trans (reachableFinset_subset_succ r source l)

theorem mem_reachableFinset_reachable {m : Nat}
    (r : Fin m → Fin m → Bool) (source : Fin m) :
    ∀ k v, v ∈ reachableFinset r source k →
      Relation.ReflTransGen (fun i j => r i j = true) source v := by
  intro k
  induction k with
  | zero =>
      intro v hv
      have : v = source := by simpa [reachableFinset] using hv
      subst v
      exact Relation.ReflTransGen.refl
  | succ k ih =>
      intro v hv
      rw [reachableFinset, mem_reachStepBool_iff] at hv
      rcases hv with hv | ⟨u, hu, huv⟩
      · exact ih v hv
      · exact Relation.ReflTransGen.tail (ih u hu) huv

/-- Executable strong-connectivity checker for a Boolean adjacency matrix. -/
def strongConnectivityCheck {m : Nat} (r : Fin m → Fin m → Bool) : Bool :=
  decide (∀ source : Fin m,
    reachableFinset r source m = Finset.univ)

theorem strongConnectivityCheck_sound {m : Nat}
    (r : Fin m → Fin m → Bool)
    (hcheck : strongConnectivityCheck r = true) :
    StronglyConnected (fun i j : Fin m => r i j = true) := by
  have hall : ∀ source : Fin m,
      reachableFinset r source m = Finset.univ := by
    exact of_decide_eq_true (by simpa [strongConnectivityCheck] using hcheck)
  intro i j
  apply mem_reachableFinset_reachable r i m j
  rw [hall i]
  simp

theorem reachableFinset_nonempty {m : Nat}
    (r : Fin m → Fin m → Bool) (source : Fin m) (k : Nat) :
    (reachableFinset r source k).Nonempty := by
  refine ⟨source, reachableFinset_mono r source (Nat.zero_le k) ?_⟩
  simp [reachableFinset]

theorem card_reachStepBool_lt_of_stronglyConnected {m : Nat}
    (r : Fin m → Fin m → Bool)
    (hsc : StronglyConnected (fun i j : Fin m => r i j = true))
    (S : Finset (Fin m)) (hne : S ≠ Finset.univ)
    (hS : S.Nonempty) :
    S.card < (reachStepBool r S).card := by
  have hproper : ∃ j, j ∉ S := by
    by_contra h
    simp only [not_exists, not_not] at h
    apply hne
    apply Finset.eq_univ_of_forall
    exact h
  obtain ⟨u, hu⟩ := hS
  obtain ⟨v, hv⟩ := hproper
  obtain ⟨a, b, ha, hb, hab⟩ :=
    exists_edge_leaving hsc ⟨u, hu⟩ ⟨v, hv⟩
  have hbStep : b ∈ reachStepBool r S :=
    (mem_reachStepBool_iff r S b).2 (Or.inr ⟨a, ha, hab⟩)
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff]
  refine ⟨b, hb, ?_⟩
  intro x hx
  rw [Finset.mem_insert] at hx
  rcases hx with rfl | hx
  · exact hbStep
  · exact subset_reachStepBool r S hx

theorem reachableFinset_eq_univ_of_stronglyConnected {m : Nat}
    (r : Fin m → Fin m → Bool)
    (hsc : StronglyConnected (fun i j : Fin m => r i j = true))
    (source : Fin m) :
    reachableFinset r source m = Finset.univ := by
  by_contra hfinal
  have hproper : ∀ k, k ≤ m →
      reachableFinset r source k ≠ Finset.univ := by
    intro k hkm hk
    apply hfinal
    apply Finset.eq_univ_of_forall
    intro v
    exact reachableFinset_mono r source hkm (by simp [hk])
  have hlower : ∀ k, k ≤ m →
      k + 1 ≤ (reachableFinset r source k).card := by
    intro k hkm
    induction k with
    | zero =>
        simp [reachableFinset]
    | succ k ih =>
        have hkm' : k ≤ m := Nat.le_trans (Nat.le_succ k) hkm
        have hgrow :
            (reachableFinset r source k).card <
              (reachableFinset r source (k + 1)).card := by
          simpa only [reachableFinset] using
            card_reachStepBool_lt_of_stronglyConnected r hsc
              (reachableFinset r source k) (hproper k hkm')
              (reachableFinset_nonempty r source k)
        have hbase := ih hkm'
        omega
  have htooLarge := hlower m (Nat.le_refl m)
  have hbound := Finset.card_le_univ (reachableFinset r source m)
  simp only [Fintype.card_fin] at hbound
  omega

theorem strongConnectivityCheck_complete {m : Nat}
    (r : Fin m → Fin m → Bool)
    (hsc : StronglyConnected (fun i j : Fin m => r i j = true)) :
    strongConnectivityCheck r = true := by
  apply decide_eq_true
  intro source
  exact reachableFinset_eq_univ_of_stronglyConnected r hsc source

theorem strongConnectivityCheck_eq_true_iff {m : Nat}
    (r : Fin m → Fin m → Bool) :
    strongConnectivityCheck r = true ↔
      StronglyConnected (fun i j : Fin m => r i j = true) :=
  ⟨strongConnectivityCheck_sound r,
    strongConnectivityCheck_complete r⟩

/-- Executable looplessness test for the same Boolean adjacency matrix. -/
def looplessCheck {m : Nat} (r : Fin m → Fin m → Bool) : Bool :=
  decide (∀ i : Fin m, r i i = false)

theorem looplessCheck_eq_true_iff {m : Nat}
    (r : Fin m → Fin m → Bool) :
    looplessCheck r = true ↔ ∀ i : Fin m, r i i = false := by
  simp [looplessCheck]

/-- The executable validity test for one directed communication round. -/
def admissibleRoundCheck {m : Nat} (r : Fin m → Fin m → Bool) : Bool :=
  looplessCheck r && strongConnectivityCheck r

theorem admissibleRoundCheck_eq_true_iff {m : Nat}
    (r : Fin m → Fin m → Bool) :
    admissibleRoundCheck r = true ↔
      (∀ i : Fin m, r i i = false) ∧
        StronglyConnected (fun i j : Fin m => r i j = true) := by
  simp [admissibleRoundCheck, looplessCheck_eq_true_iff,
    strongConnectivityCheck_eq_true_iff]

/-- A finite Boolean presentation of a dynamic graph prefix. -/
abbrev BoolGraphPrefix (m rounds : Nat) :=
  Fin rounds → Fin m → Fin m → Bool

/-- Check every round of a finite dynamic graph prefix. -/
def admissiblePrefixCheck {m rounds : Nat}
    (G : BoolGraphPrefix m rounds) : Bool :=
  decide (∀ t : Fin rounds, admissibleRoundCheck (G t) = true)

theorem admissiblePrefixCheck_eq_true_iff {m rounds : Nat}
    (G : BoolGraphPrefix m rounds) :
    admissiblePrefixCheck G = true ↔
      ∀ t : Fin rounds,
        (∀ i : Fin m, G t i i = false) ∧
          StronglyConnected (fun i j : Fin m => G t i j = true) := by
  simp [admissiblePrefixCheck, admissibleRoundCheck_eq_true_iff]

/-- Finite enumeration of all admissible graph prefixes of fixed dimensions. -/
def admissiblePrefixes (m rounds : Nat) :
    Finset (BoolGraphPrefix m rounds) :=
  Finset.univ.filter fun G => admissiblePrefixCheck G = true

theorem mem_admissiblePrefixes_iff {m rounds : Nat}
    (G : BoolGraphPrefix m rounds) :
    G ∈ admissiblePrefixes m rounds ↔
      ∀ t : Fin rounds,
        (∀ i : Fin m, G t i i = false) ∧
          StronglyConnected (fun i j : Fin m => G t i j = true) := by
  simp [admissiblePrefixes, admissiblePrefixCheck_eq_true_iff]

end DirectedCounting
