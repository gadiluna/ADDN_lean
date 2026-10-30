import Counting.InputMultisetDagLevels
import Counting.InputMultisetDagRecovery
import Counting.InputMultisetLocalCorrectness

/-! Full refinement of compact input reconstruction. Semantic history expansion
appears only in proofs. The executable search reads stored identifiers, parent
pointers, degree labels, sparse multiplicities, and the virtual input metadata. -/

namespace Counting.InputMultiset.Dag
open Counting.Executable
open scoped BigOperators

variable {Input : Type} [DecidableEq Input]

def enriched (inputOf : Nat → Input) (vista : Vista) (r i : Nat) :
    InputProtocol.FullHistory Input r := decode inputOf r (decodeNode vista (r + 1) i)

theorem mem_ids (vista : Vista) (r i : Nat) :
    i ∈ (levelNodes vista (r + 1)).toFinset ↔
      i < vista.nodes.size ∧ (vista.node i).level = r + 1 := by
  rw [List.mem_toFinset, mem_levelNodes]

variable {encode : Input → Nat} {t : Nat} {H : InputProtocol.FullHistory Input t} {vista : Vista}

theorem Rep.stored_embed (represented : Rep encode t H vista) (r i : Nat)
    (present : i ∈ (levelNodes vista (r + 1)).toFinset) :
    ∃ h ∈ InputMultisetLocal.levels t H r,
      decodeNode vista (r + 1) i = embed encode r h := by
  have member : decodeNode vista (r + 1) i ∈ Executable.decodedLevel vista (r + 1) :=
    Finset.mem_image.mpr ⟨i, present, rfl⟩
  rw [represented.decodedLevel] at member
  obtain ⟨h, hh, eq⟩ := Finset.mem_image.mp member
  exact ⟨h, hh, eq.symm⟩

theorem Rep.enriched_image (represented : Rep encode t H vista)
    (inputOf : Nat → Input) (inverse : Function.LeftInverse inputOf encode) (r : Nat) :
    (levelNodes vista (r + 1)).toFinset.image (enriched inputOf vista r) =
      InputMultisetLocal.levels t H r := by
  classical
  ext h
  constructor
  · intro hh
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hh
    obtain ⟨k, hk, eq⟩ := represented.stored_embed r i hi
    simpa only [enriched, eq, decode_embed encode inputOf inverse] using hk
  · intro hh
    have em : embed encode r h ∈ Executable.decodedLevel vista (r + 1) := by
      rw [represented.decodedLevel]
      exact Finset.mem_image.mpr ⟨h, hh, rfl⟩
    obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp em
    exact Finset.mem_image.mpr ⟨i, hi, by
      simp only [enriched, heq, decode_embed encode inputOf inverse]⟩

theorem Rep.enriched_injective (represented : Rep encode t H vista)
    (inputOf : Nat → Input) (inverse : Function.LeftInverse inputOf encode) (r : Nat) :
    Set.InjOn (enriched inputOf vista r) ((levelNodes vista (r + 1)).toFinset : Set Nat) := by
  intro i hi j hj eq
  obtain ⟨a, _, ha⟩ := represented.stored_embed r i hi
  obtain ⟨b, _, hb⟩ := represented.stored_embed r j hj
  have same : a = b := by
    simpa only [enriched, ha, hb, decode_embed encode inputOf inverse] using eq
  apply level_decoding_injOn vista represented.valid (r + 1) hi hj
  rw [ha, hb, same]

omit [DecidableEq Input] in
theorem enriched_parent (inputOf : Nat → Input) (vista : Vista) (r i : Nat) :
    (enriched inputOf vista (r + 1) i).1 =
      enriched inputOf vista r ((vista.node i).parent.getD 0) := rfl

omit [DecidableEq Input] in
theorem enriched_degree (inputOf : Nat → Input) (vista : Vista) (r i : Nat) :
    (enriched inputOf vista (r + 1) i).2.1 = (vista.node i).degree := rfl

theorem map_bundleMessages {A B : Type} (f : A → B) (value : Nat → A)
    (bundles : List (Nat × Nat)) :
    (bundleMessages value bundles).map f = bundleMessages (fun i => f (value i)) bundles := by
  induction bundles with
  | nil => rfl
  | cons e es ih =>
    simp only [bundleMessages_cons, Multiset.map_add, Multiset.map_replicate, ih]

omit [DecidableEq Input] in
theorem enriched_messages (inputOf : Nat → Input) (vista : Vista) (r i : Nat) :
    (enriched inputOf vista (r + 1) i).2.2 =
      bundleMessages (enriched inputOf vista r) (vista.node i).incoming := by
  change (bundleMessages (decodeNode vista (r + 1)) (vista.node i).incoming).map
    (decode inputOf r) = _
  exact map_bundleMessages _ _ _

omit [DecidableEq Input] in
/-- Following exactly the real-round parent pointers reads the initial input
metadata; no unfolding of the represented history is performed by the code. -/
theorem enriched_initial (inputOf : Nat → Input) (vista : Vista) (valid : vista.valid = true)
    (r i : Nat) (inside : i < vista.nodes.size) (level : (vista.node i).level = r + 1) :
    (InputProtocol.FullHistory.initial r (enriched inputOf vista r i)).2 =
      inputOf (vista.node ((ascend vista r i).getD 0)).degree := by
  induction r generalizing i with
  | zero => rfl
  | succ r ih =>
    obtain ⟨p, hp, hpi, hpl, _, _, _⟩ :=
      nodeValid_positive vista i (nodeValid_of_valid vista valid i inside) (by omega)
    change (InputProtocol.FullHistory.initial r
      (enriched inputOf vista r ((vista.node i).parent.getD 0))).2 = _
    simp only [hp, Option.getD_some, ascend, Option.bind_some]
    exact ih p (hpi.trans inside) (by omega)

theorem Rep.data_represents (represented : Rep encode t H vista)
    (inputOf : Nat → Input) (inverse : Function.LeftInverse inputOf encode) (r : Nat) :
    DagRecovery.Represents (DagRecovery.fromVista vista inputOf r) r
      (enriched inputOf vista (r + 1)) := by
  have parents : ∀ i ∈ (levelNodes vista (r + 2)).toFinset,
      ((vista.node i).parent.getD 0) ∈ (levelNodes vista (r + 1)).toFinset := by
    intro i hi
    obtain ⟨inside, level⟩ := (mem_ids vista (r + 1) i).mp hi
    obtain ⟨p, hp, hpi, hpl, _, _, _⟩ :=
      nodeValid_positive vista i (nodeValid_of_valid vista represented.valid i inside) (by omega)
    rw [hp, Option.getD_some]
    exact (mem_ids vista r p).mpr ⟨hpi.trans inside, by omega⟩
  refine ⟨represented.enriched_injective inputOf inverse (r + 1), ?_, ?_, ?_, ?_⟩
  · intro i hi j hj
    simp only [DagRecovery.fromVista, enriched_parent]
    exact ⟨congrArg (enriched inputOf vista r),
      represented.enriched_injective inputOf inverse r (parents i hi) (parents j hj)⟩
  · intro i hi
    exact (enriched_degree inputOf vista r i).symm
  · intro i hi j hj
    change countFrom (vista.node j) ((vista.node i).parent.getD 0) = _
    rw [enriched_parent, enriched_messages]
    have oldinfo := (mem_ids vista r _).mp (parents i hi)
    obtain ⟨newinside, newlevel⟩ := (mem_ids vista (r + 1) j).mp hj
    obtain ⟨_, _, _, _, _, sorted, incoming⟩ :=
      nodeValid_positive vista j (nodeValid_of_valid vista represented.valid j newinside) (by omega)
    rw [bundleMessages_count]
    · exact lookup_eq_bundleCount _ (sparse_of_countsSorted _ sorted) _
    · intro e he
      obtain ⟨ei, el⟩ := incoming e he
      have emem : e.1 ∈ (levelNodes vista (r + 1)).toFinset :=
        (mem_ids vista r e.1).mpr ⟨ei.trans newinside, by omega⟩
      exact ⟨represented.enriched_injective inputOf inverse r emem (parents i hi),
        congrArg (enriched inputOf vista r)⟩
  · intro i hi
    obtain ⟨inside, level⟩ := (mem_ids vista (r + 1) i).mp hi
    exact (enriched_initial inputOf vista represented.valid (r + 1) i inside level).symm

theorem Rep.reconstruction_eq (represented : Rep encode t H vista)
    (inputOf : Nat → Input) (inverse : Function.LeftInverse inputOf encode) (n : Nat) :
    DagRecovery.reconstruction n vista inputOf = InputMultisetLocal.reconstruction n t H := by
  apply Finset.sup_congr rfl
  intro r hr
  rw [DagRecovery.atRound_eq _ (represented.data_represents inputOf inverse r) n]
  change InputMultisetLocal.atRound n r
    ((levelNodes vista (r + 2)).toFinset.image (enriched inputOf vista (r + 1))) = _
  rw [represented.enriched_image inputOf inverse (r + 1)]

omit [DecidableEq Input] in
theorem Rep.ownInput_eq (represented : Rep encode t H vista)
    (inputOf : Nat → Input) (inverse : Function.LeftInverse inputOf encode) :
    DagRecovery.ownInput vista inputOf = (InputProtocol.FullHistory.initial t H).2 := by
  have inside : vista.bottom < vista.nodes.size := by
    have valid := represented.valid
    simp only [Vista.valid, Bool.and_eq_true, decide_eq_true_eq] at valid
    exact valid.1.1.1
  have initial := enriched_initial inputOf vista represented.valid t vista.bottom inside represented.level
  have decoded : enriched inputOf vista t vista.bottom = H := represented.decode_eq inputOf inverse
  simpa only [DagRecovery.ownInput, represented.level, Nat.add_sub_cancel, decoded] using initial.symm

theorem Rep.constant_iff (represented : Rep encode t H vista)
    (inputOf : Nat → Input) (inverse : Function.LeftInverse inputOf encode) :
    (∀ i ∈ (levelNodes vista 1).toFinset,
      inputOf (vista.node i).degree = DagRecovery.ownInput vista inputOf) ↔
    (∀ h ∈ InputMultisetLocal.levels t H 0, h.2 = (InputProtocol.FullHistory.initial t H).2) := by
  rw [← represented.enriched_image inputOf inverse 0, represented.ownInput_eq inputOf inverse]
  simp only [Finset.mem_image, forall_exists_index, and_imp]
  constructor
  · intro all h i hi eq
    rw [← eq]
    exact all i hi
  · intro all i hi
    exact all _ i hi rfl

/-- Full refinement of compact extraction to the proved local specification.
This theorem applies to any well-formed represented history, even without
connectivity; connectivity is needed only for correctness of that specification. -/
theorem Rep.recover_eq_local (represented : Rep encode t H vista)
    (inputOf : Nat → Input) (inverse : Function.LeftInverse inputOf encode) (n : Nat) :
    DagRecovery.recover n vista inputOf = InputMultisetLocal.recover n t H := by
  by_cases constant : ∀ h ∈ InputMultisetLocal.levels t H 0,
      h.2 = (InputProtocol.FullHistory.initial t H).2
  · have compact := (represented.constant_iff inputOf inverse).mpr constant
    simp only [DagRecovery.recover, InputMultisetLocal.recover, if_pos compact, if_pos constant]
    rw [represented.ownInput_eq inputOf inverse]
  · have compact : ¬ ∀ i ∈ (levelNodes vista 1).toFinset,
        inputOf (vista.node i).degree = DagRecovery.ownInput vista inputOf :=
      fun h => constant ((represented.constant_iff inputOf inverse).mp h)
    simp only [DagRecovery.recover, InputMultisetLocal.recover, if_neg compact, if_neg constant,
      represented.reconstruction_eq inputOf inverse]

/-- The executable compact-DAG recovery procedure returns the exact multiset
for every admissible physical input history, with no solver-success hypothesis. -/
theorem recoverDag_correct {V : Type} [Fintype V] [Nonempty V]
    (encode : Input → Nat) (inputOf : Nat → Input) (inverse : Function.LeftInverse inputOf encode)
    (G : Nat → V → V → Nat) (leader : V → Bool) (input : V → Input)
    (connected : ∀ t, 0 < t → DirectedCounting.StronglyConnected (fun u v => 0 < G t u v))
    (t : Nat) (late : 2 * Fintype.card V - 2 ≤ t) (observer : V) (vista : Vista)
    (represented : Rep encode t (InputProtocol.history G leader input t observer) vista) :
    DagRecovery.recover (Fintype.card V) vista inputOf =
      some ((Finset.univ : Finset V).val.map input) := by
  rw [represented.recover_eq_local inputOf inverse]
  exact InputMultisetLocal.recover_correct G leader input connected t late observer

end Counting.InputMultiset.Dag
