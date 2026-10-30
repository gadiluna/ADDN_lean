import Counting.InputMultisetDag
import Counting.InputMultisetLocalHistory
import Counting.DagSemanticsView

/-! Exact correspondence between enriched-history levels and the shifted
levels of the compact input DAG. The virtual level is excluded from all
input-history levels; real level `r` is stored at DAG level `r + 1`. -/

namespace Counting.InputMultiset.Dag

open Counting.Executable

variable {Input : Type} [DecidableEq Input]

theorem input_levels_add (r d : Nat) (H : InputProtocol.FullHistory Input (r + d)) :
    InputMultisetLocal.levels (r + d) H r = InputMultisetLocal.occurrences r d H := by
  unfold InputMultisetLocal.levels
  rw [dif_pos (Nat.le_add_right r d)]
  have hc : ∀ (a b : Nat) (eq : a = b) (h : InputProtocol.FullHistory Input (r + a)),
      InputMultisetLocal.occurrences r b
        (cast (congrArg (fun k => InputProtocol.FullHistory Input (r + k)) eq) h) =
      InputMultisetLocal.occurrences r a h := by
    intro a b eq h
    subst b
    rfl
  exact hc d (r + d - r) (Nat.add_sub_cancel_left r d).symm H

theorem input_levels_self (t : Nat) (H : InputProtocol.FullHistory Input t) :
    InputMultisetLocal.levels t H t = {H} := by
  exact (input_levels_add t 0 H).trans rfl

theorem input_levels_succ (t r : Nat) (H : InputProtocol.FullHistory Input (t + 1))
    (within : r ≤ t) :
    InputMultisetLocal.levels (t + 1) H r =
      InputMultisetLocal.levels t H.1 r ∪
        H.2.2.toFinset.biUnion (fun h => InputMultisetLocal.levels t h r) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le within
  change InputMultisetLocal.levels (r + (d + 1)) H r = _
  rw [input_levels_add]
  simp only [InputMultisetLocal.occurrences, input_levels_add]

/-- Virtual initialization shifts every real visible level by exactly one. -/
theorem levels_embed (encode : Input → Nat) (t r : Nat)
    (H : InputProtocol.FullHistory Input t) :
    TimingProtocolLocal.levels (t + 1) (embed encode t H) (r + 1) =
      (InputMultisetLocal.levels t H r).image (embed encode r) := by
  classical
  induction t generalizing r with
  | zero =>
      cases r with
      | zero => simp only [levels_self, input_levels_self, Finset.image_singleton]
      | succ r =>
          simp only [TimingProtocolLocal.levels, InputMultisetLocal.levels,
            show ¬ (r + 1 ≤ 0) by omega, show ¬ (r + 1 + 1 ≤ 0 + 1) by omega,
            dite_false, Finset.image_empty]
  | succ t ih =>
      by_cases within : r ≤ t
      · rw [levels_succ_of_le (t + 1) (r + 1) _ (by omega),
          input_levels_succ t r H within]
        simp only [embed, ih, Multiset.toFinset_map, Finset.image_biUnion,
          Finset.image_union, Finset.biUnion_image]
      · by_cases equal : r = t + 1
        · subst r
          simp only [levels_self, input_levels_self, Finset.image_singleton]
        · have above : t + 1 < r := by omega
          simp only [TimingProtocolLocal.levels, InputMultisetLocal.levels,
            show ¬ (r ≤ t + 1) by omega,
            show ¬ (r + 1 ≤ t + 1 + 1) by omega,
            dite_false, Finset.image_empty]

theorem decodedLevel_at (vista : Vista) (valid : vista.valid = true)
    (depth : Nat) (level : (vista.node vista.bottom).level = depth) (r : Nat) :
    decodedLevel vista r =
      TimingProtocolLocal.levels depth (decodeNode vista depth vista.bottom) r := by
  subst depth
  exact decodedLevel_eq_levels vista valid r

/-- The stored indices contain exactly the visible enriched histories. -/
theorem Rep.decodedLevel {encode : Input → Nat} {t : Nat}
    {H : InputProtocol.FullHistory Input t} {vista : Vista}
    (represented : Rep encode t H vista) (r : Nat) :
    decodedLevel vista (r + 1) =
      (InputMultisetLocal.levels t H r).image (embed encode r) := by
  rw [decodedLevel_at vista represented.valid (t + 1) represented.level,
    represented.history, levels_embed]

/-- Connectivity supplies the complete quotient level after `n - 1` rounds,
now stated directly for the compact DAG's stored node indices. -/
theorem Rep.levelNodes_full {V : Type} [Fintype V]
    (encode : Input → Nat) (G : Nat → V → V → Nat)
    (leader : V → Bool) (input : V → Input)
    (connected : ∀ t, 0 < t → DirectedCounting.StronglyConnected (fun u v => 0 < G t u v))
    (t r : Nat) (delay : r + (Fintype.card V - 1) ≤ t) (observer : V) (vista : Vista)
    (represented : Rep encode t (InputProtocol.history G leader input t observer) vista) :
    (levelNodes vista (r + 1)).toFinset.image (decodeNode vista (r + 1)) =
      Finset.univ.image (fun c => embed encode r (InputMultisetLocal.nodeHistory G leader input r c)) := by
  change Executable.decodedLevel vista (r + 1) = _
  rw [represented.decodedLevel,
    InputMultisetLocal.levels_full G leader input connected t r delay observer,
    Finset.image_image]
  rfl

end Counting.InputMultiset.Dag
