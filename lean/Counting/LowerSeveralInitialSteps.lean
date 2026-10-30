import Counting.LowerSeveralInitialGraph

namespace Counting.LowerSeveralInitial
open DirectedCounting LowerSeveralPhases

/-- The wraparound arc of a nonempty directed cycle. -/
theorem rotate_last_to_zero (q : Nat) (u v : Fin q)
    (last : u.val + 1 = q) (zero : v.val = 0) : finRotate q u = v := by
  cases q with
  | zero => exact Fin.elim0 u
  | succ q =>
    have hu : u = Fin.last q := Fin.ext (by simp; omega)
    have hv : v = 0 := Fin.ext zero
    rw [hu, hv, finRotate_last]

/-- Generic local observation at a cycle vertex, given its predecessor.
Only the first cycle vertex has incident leader arcs. -/
theorem delay_cycle_step {N A : Type} [Fintype N] (e : N ≃ Fin n) (k g : Nat)
    (state : LowerSeveralRelay.Vertex (Leaders k) N g → A)
    (u v : LowerSeveralRelay.Vertex (Leaders k) N g) (a b : Fin (g + n))
    (hu : ringEquiv e k g u = .inr a) (hv : ringEquiv e k g v = .inr b)
    (adjacent : finRotate (g + n) a = b) :
    step (delayGraph e k g) state v =
      (state v, (if b.val = 0 then k + 2 else 0) + 1,
        (if b.val = 0 then ∑ l : Leaders k, ({state (.inl (.inl l))} : Multiset A) else 0) +
        {state u}) := by
  have inverse : (ringEquiv e k g).symm (.inr ((finRotate (g + n)).symm b)) = u := by
    rw [← adjacent, Equiv.symm_apply_apply, ← hu, Equiv.symm_apply_apply]
  unfold step delayGraph
  rw [relabel_degree, relabel_incoming, hv, cycleStar_nonleader_degree,
    cycleStar_nonleader_incoming, inverse]
  simp

theorem delay_leader_step {N A : Type} [Fintype N] (e : N ≃ Fin n) (k g : Nat)
    (hg : 0 < g) (state : LowerSeveralRelay.Vertex (Leaders k) N g → A) (l : Leaders k) :
    step (delayGraph e k g) state (.inl (.inl l)) =
      (state (.inl (.inl l)), 1, {state (.inr ⟨0, hg⟩)}) := by
  have hq : 0 < g + n := by omega
  have hz : ringEquiv e k g (.inr ⟨0, hg⟩) = .inr ⟨0, hq⟩ := rfl
  unfold step delayGraph
  rw [relabel_degree, relabel_incoming, ringEquiv_leader,
    cycleStar_leader_degree _ _ hq, cycleStar_leader_incoming _ _ hq,
    ← hz, Equiv.symm_apply_apply]

theorem delay_original_first_step {N A : Type} [Fintype N] (e : N ≃ Fin n) (k g : Nat)
    (hg : 0 < g) (state : LowerSeveralRelay.Vertex (Leaders k) N g → A)
    (v : N) (first : (e v).val = 0) :
    step (delayGraph e k g) state (.inl (.inr v)) =
      (state (.inl (.inr v)), 1, {state (.inr ⟨g - 1, by omega⟩)}) := by
  have h := delay_cycle_step e k g state (.inr ⟨g - 1, by omega⟩) (.inl (.inr v))
    ((⟨g - 1, by omega⟩ : Fin g).castAdd n) (Fin.natAdd g (e v)) rfl rfl
    (LowerSeveralCycles.rotate_of_next _ _ _ (by simp only [Fin.val_castAdd, Fin.val_natAdd]; omega))
  simpa only [Fin.val_natAdd, first, Nat.add_zero, if_neg (by omega : g ≠ 0),
    zero_add] using h

theorem delay_original_next_step {N A : Type} [Fintype N] (e : N ≃ Fin n) (k g : Nat)
    (hg : 0 < g) (state : LowerSeveralRelay.Vertex (Leaders k) N g → A)
    (u v : N) (next : (e u).val + 1 = (e v).val) :
    step (delayGraph e k g) state (.inl (.inr v)) =
      (state (.inl (.inr v)), 1, {state (.inl (.inr u))}) := by
  have h := delay_cycle_step e k g state (.inl (.inr u)) (.inl (.inr v))
    (Fin.natAdd g (e u)) (Fin.natAdd g (e v)) rfl rfl
    (LowerSeveralCycles.rotate_of_next _ _ _ (by simp only [Fin.val_natAdd]; omega))
  simpa only [Fin.val_natAdd, if_neg (by omega : g + (e v).val ≠ 0), zero_add] using h

theorem delay_relay_first_step {N A : Type} [Fintype N] (e : N ≃ Fin n) (k g : Nat)
    (hg : 0 < g) (state : LowerSeveralRelay.Vertex (Leaders k) N g → A)
    (last : N) (hlast : (e last).val + 1 = n) :
    step (delayGraph e k g) state (.inr ⟨0, hg⟩) =
      (state (.inr ⟨0, hg⟩), k + 3,
        (∑ l : Leaders k, ({state (.inl (.inl l))} : Multiset A)) + {state (.inl (.inr last))}) := by
  have h := delay_cycle_step e k g state (.inl (.inr last)) (.inr ⟨0, hg⟩)
    (Fin.natAdd g (e last)) ((⟨0, hg⟩ : Fin g).castAdd n) rfl rfl
    (rotate_last_to_zero _ _ _ (by simp only [Fin.val_natAdd]; omega) rfl)
  simpa using h

theorem delay_relay_next_step {N A : Type} [Fintype N] (e : N ≃ Fin n) (k g : Nat)
    (state : LowerSeveralRelay.Vertex (Leaders k) N g → A)
    (i j : Fin g) (next : i.val + 1 = j.val) :
    step (delayGraph e k g) state (.inr j) = (state (.inr j), 1, {state (.inr i)}) := by
  have h := delay_cycle_step e k g state (.inr i) (.inr j) (i.castAdd n) (j.castAdd n) rfl rfl
    (LowerSeveralCycles.rotate_of_next _ _ _ next)
  simpa only [Fin.val_castAdd, if_neg (by omega : j.val ≠ 0), zero_add] using h

end Counting.LowerSeveralInitial
