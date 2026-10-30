import Counting.InputMultisetLocalFinite
import Counting.InputMultisetLocalHistory

namespace Counting.InputMultisetLocal
open DirectedCounting DirectedCounting.PaperHistory
open scoped BigOperators

variable {V Input : Type} [Fintype V] [Nonempty V] [DecidableEq Input]
variable (G : Nat → V → V → Nat) (leader : V → Bool) (input : V → Input)

noncomputable def fullLevel (r : Nat) : Finset (InputProtocol.FullHistory Input r) :=
  Finset.univ.image (nodeHistory G leader input r)

omit [Nonempty V] in
theorem nodeHistory_mem_fullLevel (r : Nat)
    (c : Node G (fun v => (leader v, input v)) r) :
    nodeHistory G leader input r c ∈ fullLevel G leader input r :=
  Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩

omit [Nonempty V] in
theorem sum_fullLevel {M : Type*} [AddCommMonoid M] (r : Nat)
    (f : InputProtocol.FullHistory Input r → M) :
    (∑ h ∈ fullLevel G leader input r, f h) =
      ∑ c : Node G (fun v => (leader v, input v)) r, f (nodeHistory G leader input r c) := by
  classical
  exact Finset.sum_image (fun _ _ _ _ heq => nodeHistory_injective G leader input r heq)

theorem valid_counts_eq (r : Nat)
    (connected : StronglyConnected (fun u v => 0 < G (r + 1) u v))
    (w : ∀ h ∈ fullLevel G leader input (r + 1), Nat)
    (valid : Valid (Fintype.card V) r (fullLevel G leader input (r + 1)) w) :
    ∀ c : Node G (fun v => (leader v, input v)) (r + 1),
      weightAt (fullLevel G leader input (r + 1)) w (nodeHistory G leader input (r + 1) c) =
        anonymity G (fun v => (leader v, input v)) (r + 1) c := by
  classical
  let counts := fun c : Node G (fun v => (leader v, input v)) (r + 1) =>
    weightAt (fullLevel G leader input (r + 1)) w (nodeHistory G leader input (r + 1) c)
  have flat : InputMultisetRecovery.Flat G (fun v => (leader v, input v)) r := by
    intro i j hp
    apply nodeHistory_injective G leader input (r + 1)
    exact valid.1 _ (nodeHistory_mem_fullLevel G leader input _ i)
      _ (nodeHistory_mem_fullLevel G leader input _ j) (by simp only [nodeHistory_parent, hp])
  have total : ∑ c, counts c = Fintype.card V := by
    simpa only [sum_fullLevel] using valid.2.1
  have flow : FlatLevel.Flow
      (fun i j => (InputMultisetRecovery.weight G (fun v => (leader v, input v)) r i j : ℚ))
      (fun i => (outdegreeLabel G (fun v => (leader v, input v)) r i : ℚ))
      (fun i => (counts i : ℚ)) := by
    intro i
    have hi := valid.2.2 _ (nodeHistory_mem_fullLevel G leader input (r + 1) i)
    rw [sum_fullLevel] at hi
    simp only [nodeHistory_parent, nodeHistory_red, nodeHistory_degree] at hi
    dsimp only [InputMultisetRecovery.weight, counts]
    exact_mod_cast hi
  have eq := InputMultisetRecovery.normalized_flow_unique G
    (fun v => (leader v, input v)) r flat connected (fun i => (counts i : ℚ))
    flow (by exact_mod_cast total)
  intro c
  exact_mod_cast congrFun eq c

theorem candidateOutput_eq (r : Nat)
    (connected : StronglyConnected (fun u v => 0 < G (r + 1) u v))
    (w : ∀ h ∈ fullLevel G leader input (r + 1), Nat)
    (valid : Valid (Fintype.card V) r (fullLevel G leader input (r + 1)) w) :
    candidateOutput r (fullLevel G leader input (r + 1)) w =
      (Finset.univ : Finset V).val.map input := by
  unfold candidateOutput
  rw [sum_fullLevel]
  simp only [valid_counts_eq G leader input r connected w valid, nodeHistory_initial]
  exact true_multiset G leader input (r + 1)

omit [Nonempty V] in
theorem solutions_nonempty (r : Nat)
    (flat : InputMultisetRecovery.Flat G (fun v => (leader v, input v)) r) :
    (solutions (Fintype.card V) r (fullLevel G leader input (r + 1))).Nonempty := by
  classical
  let s := fullLevel G leader input (r + 1)
  let w : ∀ h ∈ s, Nat := fun h _ =>
    ∑ c : Node G (fun v => (leader v, input v)) (r + 1),
      if nodeHistory G leader input (r + 1) c = h then
        anonymity G (fun v => (leader v, input v)) (r + 1) c else 0
  have correct : ∀ c : Node G (fun v => (leader v, input v)) (r + 1),
      weightAt s w (nodeHistory G leader input (r + 1) c) =
        anonymity G (fun v => (leader v, input v)) (r + 1) c := by
    intro c
    rw [weightAt_mem _ _ _ (nodeHistory_mem_fullLevel G leader input _ c)]
    simp [w, (nodeHistory_injective G leader input (r + 1)).eq_iff]
  refine ⟨w, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
  · apply Finset.mem_pi.mpr
    intro h hh
    obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hh
    have hc := correct c
    rw [weightAt_mem _ _ _ (nodeHistory_mem_fullLevel G leader input _ c)] at hc
    rw [hc, Finset.mem_range]
    have upper : anonymity G (fun v => (leader v, input v)) (r + 1) c ≤ Fintype.card V := by
      rw [← total_anonymity G (fun v => (leader v, input v)) (r + 1)]
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
    omega
  · refine ⟨?_, ?_, ?_⟩
    · intro i hi j hj hp
      obtain ⟨ci, _, rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨cj, _, rfl⟩ := Finset.mem_image.mp hj
      simp only [nodeHistory_parent] at hp
      exact congrArg (nodeHistory G leader input (r + 1))
        (flat (nodeHistory_injective G leader input r hp))
    · change (∑ h ∈ fullLevel G leader input (r + 1), weightAt s w h) = _
      rw [sum_fullLevel]
      simp only [correct]
      exact total_anonymity G (fun v => (leader v, input v)) (r + 1)
    · intro i hi
      obtain ⟨ci, _, rfl⟩ := Finset.mem_image.mp hi
      change (∑ j ∈ fullLevel G leader input (r + 1),
        (j.2.2.count (nodeHistory G leader input (r + 1) ci).1) * weightAt s w j) = _
      rw [sum_fullLevel]
      simp only [nodeHistory_parent, nodeHistory_red, nodeHistory_degree, correct]
      have hci := correct ci
      dsimp only [s] at hci
      rw [hci]
      exact InputMultisetRecovery.natural_flow G (fun v => (leader v, input v)) r flat ci

theorem reconstruction_eq
    (connected : ∀ t, 0 < t → StronglyConnected (fun u v => 0 < G t u v))
    (t : Nat) (late : 2 * Fintype.card V - 2 ≤ t) (observer : V)
    (nonconstant : ∃ u v, input u ≠ input v) :
    reconstruction (Fintype.card V) t (InputProtocol.history G leader input t observer) =
      (Finset.univ : Finset V).val.map input := by
  classical
  have hn : 0 < Fintype.card V := Fintype.card_pos
  have full : ∀ r ∈ Finset.range (Fintype.card V - 1),
      levels t (InputProtocol.history G leader input t observer) (r + 1) =
        fullLevel G leader input (r + 1) := by
    intro r hr
    apply levels_full G leader input connected
    simp only [Finset.mem_range] at hr
    omega
  apply reconstruction_eq_of_certificates
  · intro r hr
    rw [full r hr]
    intro w hw
    exact candidateOutput_eq G leader input r (connected _ (by omega)) w
      (Finset.mem_filter.mp hw).2
  · obtain ⟨u, v, huv⟩ := nonconstant
    have different : ∃ u v, (leader u, input u) ≠ (leader v, input v) :=
      ⟨u, v, fun h => huv (congrArg Prod.snd h)⟩
    obtain ⟨r, hr, hflat⟩ := InputMultisetRecovery.exists_early_flat_of_nonconstant
      G (fun v => (leader v, input v)) different
    have hrange : r ∈ Finset.range (Fintype.card V - 1) := Finset.mem_range.mpr (by omega)
    refine ⟨r, hrange, ?_⟩
    rw [full r hrange]
    obtain ⟨w, hw⟩ := solutions_nonempty G leader input r hflat
    exact ⟨w, hw, candidateOutput_eq G leader input r (connected _ (by omega)) w
      (Finset.mem_filter.mp hw).2⟩

/-- The executable local extractor always returns the exact input multiset
from depth `2n - 2`, using only the computed population and its own history. -/
theorem recover_correct
    (connected : ∀ t, 0 < t → StronglyConnected (fun u v => 0 < G t u v))
    (t : Nat) (late : 2 * Fintype.card V - 2 ≤ t) (observer : V) :
    recover (Fintype.card V) t (InputProtocol.history G leader input t observer) =
      some ((Finset.univ : Finset V).val.map input) := by
  classical
  have hn : 0 < Fintype.card V := Fintype.card_pos
  have full0 := levels_full G leader input connected t 0 (by omega) observer
  unfold recover
  split_ifs with constant
  · have all_constant : ∀ v, input v = input observer := by
      intro v
      have mem : InputProtocol.history G leader input 0 v ∈
          levels t (InputProtocol.history G leader input t observer) 0 := by
        rw [full0]
        exact Finset.mem_image.mpr ⟨classOf G _ 0 v, Finset.mem_univ _,
          nodeHistory_classOf G leader input 0 v⟩
      simpa only [InputProtocol.history, InputProtocol.initial_history] using constant _ mem
    simp only [InputProtocol.initial_history]
    congr 1
    exact (InputMultisetRecovery.populationMultiset_constant input (input observer) all_constant).symm
  · have nonconstant : ∃ u v, input u ≠ input v := by
      by_contra h
      push Not at h
      apply constant
      intro H hH
      rw [full0] at hH
      obtain ⟨c, _, rfl⟩ := Finset.mem_image.mp hH
      change input c.out = _
      simpa only [InputProtocol.initial_history] using h c.out observer
    have recovered := reconstruction_eq G leader input connected t late observer nonconstant
    simp only [recovered, Multiset.card_map, Finset.card_val, Finset.card_univ, ↓reduceIte]

end Counting.InputMultisetLocal
