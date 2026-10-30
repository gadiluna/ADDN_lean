import Counting.LowerSeveralCycles

/-! The initial-delay graph: a directed nonleader cycle, with unit arcs
in both directions between every leader and the first relay. -/

namespace Counting.LowerSeveralInitial
open DirectedCounting LowerSeveralPhases

def cycleStar (ell q : Nat) : (Fin ell ⊕ Fin q) → (Fin ell ⊕ Fin q) → Nat
  | .inl _, .inl _ => 0
  | .inl _, .inr v => if v.val = 0 then 1 else 0
  | .inr u, .inl _ => if u.val = 0 then 1 else 0
  | .inr u, .inr v => LowerSeveralCycles.edge q u v

theorem sum_at_zero {A : Type} [AddCommMonoid A] (q : Nat) (hq : 0 < q) (a : Fin q → A) :
    (∑ v : Fin q, if v.val = 0 then a v else 0) = a ⟨0, hq⟩ := by
  have eq : ∀ v : Fin q, v.val = 0 ↔ v = ⟨0, hq⟩ := by intro v; simp [Fin.ext_iff]
  simp only [eq]
  simp

theorem cycleStar_leader_degree (ell q : Nat) (hq : 0 < q) (l : Fin ell) :
    (∑ v, cycleStar ell q (.inl l) v) = 1 := by
  rw [Fintype.sum_sum_type]
  simpa only [cycleStar, Finset.sum_const_zero, zero_add] using sum_at_zero q hq (fun _ => (1 : Nat))

theorem cycleStar_nonleader_degree (ell q : Nat) (u : Fin q) :
    (∑ v, cycleStar ell q (.inr u) v) = (if u.val = 0 then ell else 0) + 1 := by
  rw [Fintype.sum_sum_type]
  simp [cycleStar, LowerSeveralCycles.degree]

theorem cycleStar_leader_incoming {A : Type} (ell q : Nat) (hq : 0 < q)
    (state : Fin ell ⊕ Fin q → A) (l : Fin ell) :
    incoming (cycleStar ell q) state (.inl l) = {state (.inr ⟨0, hq⟩)} := by
  unfold incoming
  rw [Fintype.sum_sum_type]
  simp only [cycleStar, Multiset.replicate_zero, Finset.sum_const_zero, zero_add]
  calc
    _ = ∑ v : Fin q, if v.val = 0 then ({state (.inr v)} : Multiset A) else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      split_ifs <;> simp
    _ = _ := sum_at_zero q hq _

theorem cycleStar_nonleader_incoming {A : Type} (ell q : Nat)
    (state : Fin ell ⊕ Fin q → A) (v : Fin q) :
    incoming (cycleStar ell q) state (.inr v) =
      (if v.val = 0 then ∑ l : Fin ell, ({state (.inl l)} : Multiset A) else 0) +
      {state (.inr ((finRotate q).symm v))} := by
  unfold incoming
  rw [Fintype.sum_sum_type]
  have hcycle := LowerSeveralCycles.incoming_eq q (fun u => state (.inr u)) v
  unfold incoming at hcycle
  dsimp only [cycleStar]
  rw [hcycle]
  by_cases hv : v.val = 0 <;> simp [hv]

theorem cycleStar_connected (ell q : Nat) (hq : 0 < q) :
    StronglyConnected (fun u v => 0 < cycleStar ell q u v) := by
  let z : Fin q := ⟨0, hq⟩
  have cycle : ∀ u v : Fin q, Relation.ReflTransGen
      (fun a b => 0 < cycleStar ell q a b) (.inr u) (.inr v) := by
    intro u v
    induction LowerSeveralCycles.connected q u v with
    | refl => exact .refl
    | tail _ edge ih => exact ih.tail edge
  have toZero : ∀ u, Relation.ReflTransGen
      (fun a b => 0 < cycleStar ell q a b) u (.inr z) := by
    intro u
    cases u with
    | inl l => exact .single (by simp [cycleStar, z])
    | inr u => exact cycle u z
  have fromZero : ∀ v, Relation.ReflTransGen
      (fun a b => 0 < cycleStar ell q a b) (.inr z) v := by
    intro v
    cases v with
    | inl l => exact .single (by simp [cycleStar, z])
    | inr v => exact cycle z v
  exact fun u v => (toZero u).trans (fromZero v)

theorem cycleStar_valid (k q : Nat) (hq : 2 ≤ q) : RoundValid (cycleStar (k + 2) q) (k + 2) where
  connected := cycleStar_connected _ _ (by omega)
  loopless := by
    intro u
    cases u with
    | inl _ => rfl
    | inr u => exact LowerSeveralCycles.loopless q hq u
  multiplicity := by
    intro u v
    cases u <;> cases v <;> simp only [cycleStar]
    · omega
    · split_ifs <;> omega
    · split_ifs <;> omega
    · exact (LowerSeveralCycles.multiplicity _ _ _).trans (by omega)
  degree := by
    intro u
    have hone : 1 ≤ (k + 2) ^ 2 := by
      simpa using Nat.pow_le_pow_left (show 1 ≤ k + 2 by omega) 2
    cases u with
    | inl l => rw [cycleStar_leader_degree _ _ (by omega)]; exact hone
    | inr u => rw [cycleStar_nonleader_degree]; split_ifs <;> nlinarith

/-- Relays occupy the first g cycle positions; original nonleaders follow. -/
def ringEquiv {N : Type} (e : N ≃ Fin n) (k g : Nat) :
    LowerSeveralRelay.Vertex (Leaders k) N g ≃ (Leaders k ⊕ Fin (g + n)) :=
  (Equiv.sumAssoc _ _ _).trans
    (Equiv.sumCongr (Equiv.refl _) ((Equiv.sumComm _ _).trans
      ((Equiv.sumCongr (Equiv.refl _) e).trans finSumFinEquiv)))

@[simp] theorem ringEquiv_leader {N : Type} (e : N ≃ Fin n) (k g : Nat) (l : Leaders k) :
    ringEquiv e k g (.inl (.inl l)) = .inl l := rfl

@[simp] theorem ringEquiv_nonleader {N : Type} (e : N ≃ Fin n) (k g : Nat) (v : N) :
    ringEquiv e k g (.inl (.inr v)) = .inr (Fin.natAdd g (e v)) := rfl

@[simp] theorem ringEquiv_relay {N : Type} (e : N ≃ Fin n) (k g : Nat) (j : Fin g) :
    ringEquiv e k g (.inr j) = .inr (j.castAdd n) := rfl

@[simp] theorem ringEquiv_symm_leader {N : Type} (e : N ≃ Fin n) (k g : Nat) (l : Leaders k) :
    (ringEquiv e k g).symm (.inl l) = .inl (.inl l) := by
  exact (ringEquiv e k g).symm_apply_apply (.inl (.inl l))

def unitFin : Unit ≃ Fin 1 where
  toFun _ := 0
  invFun _ := ()
  left_inv u := by cases u; rfl
  right_inv _ := Subsingleton.elim _ _

def delayGraph {N : Type} (e : N ≃ Fin n) (k g : Nat) :=
  relabel (ringEquiv e k g) (cycleStar (k + 2) (g + n))

theorem delayGraph_valid {N : Type} [Fintype N] (e : N ≃ Fin n) (k g : Nat)
    (hg : 0 < g) (hn : 0 < n) : RoundValid (delayGraph e k g) (k + 2) :=
  relabel_valid _ _ _ (cycleStar_valid k (g + n) (by omega))

def initialSmall (k g : Nat) : Small k g → Small k g → Nat :=
  if 0 < g then delayGraph unitFin k g else firstSmall k g

def initialLarge (k g : Nat) : Large k g → Large k g → Nat :=
  if 0 < g then delayGraph (Equiv.refl (Leaders k)) k g else firstLarge k g 0

theorem initialSmall_valid (k g : Nat) : RoundValid (initialSmall k g) (k + 2) := by
  unfold initialSmall
  split_ifs with hg
  · exact delayGraph_valid _ _ _ hg (by omega)
  · exact firstSmall_valid k g

theorem initialLarge_valid (k g : Nat) : RoundValid (initialLarge k g) (k + 2) := by
  unfold initialLarge
  split_ifs with hg
  · exact delayGraph_valid _ _ _ hg (by omega)
  · exact firstLarge_valid k g 0

end Counting.LowerSeveralInitial
