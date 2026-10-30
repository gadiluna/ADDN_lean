import Counting.Vista

/-! The all-leaders test is sound at round ell even when n is unknown. -/

namespace Counting
open DirectedCounting

/-- Flooding from an arbitrary nonempty initial set needs at most the number
of initially uninformed agents, rather than n-1 rounds. -/
theorem flooding_after_remaining {V : Type} [Fintype V]
    (edge : Nat → V → V → Prop) (informed : Nat → Finset V)
    (hsc : ∀ t, StronglyConnected (edge t))
    (initial : (informed 0).Nonempty)
    (mono : ∀ t, informed t ⊆ informed (t + 1))
    (deliver : ∀ t ⦃u v⦄, u ∈ informed t → edge t u v → v ∈ informed (t + 1))
    (d : Nat) (budget : Fintype.card V ≤ (informed 0).card + d) :
    informed d = Finset.univ := by
  classical
  by_contra hlast
  have proper : ∀ t, t ≤ d → informed t ≠ Finset.univ := by
    intro t ht heq
    have hs := informed_mono_trans informed mono ht
    have hu : Finset.univ ⊆ informed d := by simpa [heq] using hs
    exact hlast (Finset.Subset.antisymm (Finset.subset_univ _) hu)
  have nonempty : ∀ t, (informed t).Nonempty :=
    fun t => initial.mono (informed_mono_trans informed mono (Nat.zero_le t))
  have grows : ∀ t, t ≤ d → (informed 0).card + t ≤ (informed t).card := by
    intro t ht
    induction t with
    | zero => simp
    | succ t ih =>
        have htd : t ≤ d := by omega
        have hstep := informed_card_strictly_grows edge informed hsc mono deliver
          (nonempty t) (proper t htd)
        have hi := ih htd
        omega
  have hlarge := grows d le_rfl
  have hcard : (informed d).card = Fintype.card V :=
    Nat.le_antisymm (Finset.card_le_univ _) (by omega)
  exact hlast (Finset.eq_univ_of_card _ hcard)

noncomputable def nonleaderInformed {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool) (t : Nat) : Finset V := by
  classical
  exact Finset.univ.filter (fun x => ∃ source, leader source = false ∧
    TemporalReach (fun r u v => 0 < G r u v) 0 source t x)

@[simp] theorem nonleaderInformed_zero {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool) :
    nonleaderInformed G leader 0 = Finset.univ.filter (fun x => leader x = false) := by
  classical
  ext x
  simp only [nonleaderInformed, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨s, hs, hp⟩
    cases hp
    exact hs
  · intro hx
    exact ⟨x, hx, TemporalReach.zero⟩

theorem nonleader_card_add_leader_card {V : Type} [Fintype V]
    (leader : V → Bool) :
    (Finset.univ.filter (fun x => leader x = false)).card + leaderCount leader =
      Fintype.card V := by
  classical
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset V))
    (p := fun x => leader x = false)
  simpa [leaderCount] using h

/-- If n>ell, every observer has seen a nonleader by round ell. -/
theorem nonleader_visible_by_leader_count {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool) (ell : Nat)
    (valid : Admissible ell G leader) (larger : ell < Fintype.card V) (observer : V) :
    Sees (r := 0) false ell (history G leader (0 + ell) observer) := by
  classical
  let informed := nonleaderInformed G leader
  let edge := fun t u v => 0 < G (t + 1) u v
  have count0 : (informed 0).card + ell = Fintype.card V := by
    simpa [informed, ← valid.leaders] using nonleader_card_add_leader_card leader
  have initial : (informed 0).Nonempty := Finset.card_pos.mp (by omega)
  have mono : ∀ t, informed t ⊆ informed (t + 1) := by
    intro t x hx
    simp only [informed, nonleaderInformed, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    obtain ⟨s, hs, hp⟩ := hx
    exact ⟨s, hs, TemporalReach.stay hp⟩
  have deliver : ∀ t ⦃u v⦄, u ∈ informed t → edge t u v → v ∈ informed (t + 1) := by
    intro t u v hu huv
    simp only [informed, nonleaderInformed, Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
    obtain ⟨s, hs, hp⟩ := hu
    exact ⟨s, hs, TemporalReach.send hp (by simpa [edge] using huv)⟩
  have all := flooding_after_remaining edge informed
    (fun t => valid.connected (t + 1) (by omega)) initial mono deliver ell (by omega)
  have seen : observer ∈ informed ell := by rw [all]; exact Finset.mem_univ observer
  simp only [informed, nonleaderInformed, Finset.mem_filter, Finset.mem_univ, true_and] at seen
  obtain ⟨s, hs, hp⟩ := seen
  exact (sees_iff_causal_support G leader 0 ell observer false).mpr ⟨s, hs.symm, hp⟩

/-- The semantic all-leaders test succeeds exactly on all-leader networks. -/
theorem all_leaders_test_iff {V : Type} [Fintype V]
    (G : Nat → V → V → Nat) (leader : V → Bool) (ell : Nat)
    (valid : Admissible ell G leader) (observer : V) :
    (¬ Sees (r := 0) false ell (history G leader (0 + ell) observer)) ↔ Fintype.card V = ell := by
  classical
  constructor
  · intro hn
    have hle := valid.leaderCount_le_card
    by_contra he
    exact hn (nonleader_visible_by_leader_count G leader ell valid (by omega) observer)
  · intro he hseen
    obtain ⟨s, hs, _⟩ := (sees_iff_causal_support G leader 0 ell observer false).mp hseen
    have hc := nonleader_card_add_leader_card leader
    have hz : (Finset.univ.filter (fun x => leader x = false)).card = 0 := by
      rw [valid.leaders] at hc
      omega
    have hm : s ∈ Finset.univ.filter (fun x => leader x = false) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hs.symm
    rw [Finset.card_eq_zero.mp hz] at hm
    exact Finset.notMem_empty s hm

end Counting
