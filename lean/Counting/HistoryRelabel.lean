import Counting.Network

/-! Physical relabeling changes neither anonymous observations nor leader
counts. The history theorem needs equality only on the finite prefix being
observed, permitting different admissible continuations after that prefix. -/
namespace Counting
open DirectedCounting
open scoped BigOperators

theorem leaderCount_equiv {V W : Type} [Fintype V] [Fintype W]
    (e : V ≃ W) (left : V → Bool) (right : W → Bool)
    (labels : ∀ x, left x = right (e x)) : leaderCount left = leaderCount right := by
  classical
  simp only [leaderCount, Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Fintype.sum_equiv e _ _ (fun x => by rw [labels x])

theorem connected_equiv {V W : Type} (e : V ≃ W) (left : V → V → Nat) (right : W → W → Nat)
    (edges : ∀ x y, left x y = right (e x) (e y))
    (connected : StronglyConnected (fun x y => 0 < right x y)) :
    StronglyConnected (fun x y => 0 < left x y) := by
  intro x y
  have path := Relation.ReflTransGen.lift e.symm
    (show (fun u v => 0 < right u v) ≤
      Function.onFun (fun u v => 0 < left u v) e.symm from by
        intro u v positive
        simpa only [Function.onFun, edges, e.apply_symm_apply] using positive)
    (e x) (e y) (connected (e x) (e y))
  simpa only [Function.onFun, e.symm_apply_apply] using path

theorem history_equiv {V W : Type} [Fintype V] [Fintype W]
    (e : V ≃ W) (G : Nat → V → V → Nat) (H : Nat → W → W → Nat)
    (left : V → Bool) (right : W → Bool) (t : Nat)
    (labels : ∀ x, left x = right (e x))
    (edges : ∀ r, 0 < r → r ≤ t → ∀ x y, G r x y = H r (e x) (e y)) (x : V) :
    history G left t x = history H right t (e x) := by
  induction t generalizing x with
  | zero => exact labels x
  | succ t ih =>
      have earlier : ∀ y, history G left t y = history H right t (e y) :=
        fun y => ih (fun r positive within => edges r positive (by omega)) y
      change (_, _, _) = (_, _, _)
      apply Prod.ext (earlier x)
      apply Prod.ext
      · exact Fintype.sum_equiv e _ _ (fun y => edges (t+1) (by omega) le_rfl x y)
      · unfold incoming
        exact Fintype.sum_equiv e _ _ (fun y => by
          rw [edges (t+1) (by omega) le_rfl y x, earlier y])

end Counting
