import Counting.ExecutableRefinementCertificate

namespace Counting.Executable
open Counting.TimingProtocolLocal
open scoped BigOperators

noncomputable def extendCoordinates (vista : Vista) (r : Nat)
    (x : Fin (levelNodes vista r).length → ℚ) (H : Counting.FullHistory r) : ℚ := by
  classical
  exact if found : ∃ j : Fin (levelNodes vista r).length,
      decodeNode vista r (levelNodes vista r)[j.val] = H then x found.choose else 0

theorem extendCoordinates_decode (vista : Vista) (valid : vista.valid = true) (r : Nat)
    (x : Fin (levelNodes vista r).length → ℚ) (j : Fin (levelNodes vista r).length) :
    extendCoordinates vista r x (decodeNode vista r (levelNodes vista r)[j.val]) = x j := by
  classical
  unfold extendCoordinates
  have found : ∃ k : Fin (levelNodes vista r).length,
      decodeNode vista r (levelNodes vista r)[k.val] = decodeNode vista r (levelNodes vista r)[j.val] :=
    ⟨j, rfl⟩
  rw [dif_pos found]
  have equal := level_decoding_injOn vista valid r
    (List.mem_toFinset.mpr (List.getElem_mem found.choose.isLt))
    (List.mem_toFinset.mpr (List.getElem_mem j.isLt)) found.choose_spec
  have same : found.choose = j := (levelNodes_nodup vista r).injective_get equal
  rw [same]

theorem intrinsic_of_nodeAnchorSolution (vista : Vista) (valid : vista.valid = true)
    (leaders r : Nat) (z : Counting.FullHistory (r + 1) → ℚ)
    (solution : NodeAnchorSolution vista (r + 1) leaders (fun i => z (decodeNode vista (r + 1) i))) :
    AnchorSolution leaders r (decodedLevel vista) z := by
  classical
  constructor
  · intro H hH
    obtain ⟨old, oldInside, oldLevel, rfl⟩ := (mem_decodedLevel vista r H).mp hH
    have oldPresent := (mem_levelNodes vista r old).mpr ⟨oldInside, oldLevel⟩
    have equation := solution.1 old (by simpa only [Nat.add_sub_cancel] using oldPresent)
    rw [sum_decodedLevel vista valid, sum_decodedLevel vista valid]
    convert equation using 1
    · apply congrArg List.sum
      apply List.map_congr_left
      intro i hi
      have info := (mem_levelNodes vista (r + 1) i).mp hi
      rw [red_decode vista valid r old i oldInside info.1 oldLevel info.2]
    · apply congrArg List.sum
      apply List.map_congr_left
      intro i hi
      simp only [parent_decode_eq_iff vista valid r old i oldPresent hi, degree_decode]
  · rw [Finset.sum_filter, sum_decodedLevel vista valid]
    convert solution.2 using 1
    apply congrArg List.sum
    apply List.map_congr_left
    intro i hi
    have info := (mem_levelNodes vista (r + 1) i).mp hi
    rw [input_decode vista valid (r + 1) i info.1 info.2]

theorem intrinsic_of_rows (vista : Vista) (valid : vista.valid = true) (leaders r : Nat)
    (x : Fin (levelNodes vista (r + 1)).length → ℚ)
    (rows : RowsSatisfied (levelNodes vista (r + 1)).length (anchorRows vista (r + 1) leaders) x) :
    AnchorSolution leaders r (decodedLevel vista) (extendCoordinates vista (r + 1) x) := by
  apply intrinsic_of_nodeAnchorSolution vista valid leaders r
  apply (anchorRows_satisfied_iff _ _ _ _).mp
  have equal : (fun j : Fin (levelNodes vista (r + 1)).length =>
      extendCoordinates vista (r + 1) x (decodeNode vista (r + 1) (levelNodes vista (r + 1))[j.val])) = x := by
    funext j
    exact extendCoordinates_decode vista valid (r + 1) x j
  rw [equal]
  exact rows

theorem fullCertificate_solver (vista : Vista) (valid : vista.valid = true) (leaders candidate last r : Nat)
    (c : ∀ k, Counting.FullHistory k → Nat)
    (certificate : FullCertificate leaders candidate last r (decodedLevel vista) c) :
    solveLinear? (levelNodes vista (r + 1)).length (anchorRows vista (r + 1) leaders) =
      some (vectorArray (fun j => (c (r + 1)
        (decodeNode vista (r + 1) (levelNodes vista (r + 1))[j.val]) : ℚ))) := by
  apply solveLinear_complete_of_unique _ _ (anchorRows_sized _ _ _) _
  · exact (anchorRows_satisfied_iff _ _ _ _).mpr
      (nodeAnchorSolution_of_intrinsic vista valid leaders r _ certificate.candidate_anchor_solution)
  · intro y hy
    funext j
    have present := (List.getElem_mem j.isLt : (levelNodes vista (r + 1))[j.val] ∈ levelNodes vista (r + 1))
    have info := (mem_levelNodes vista (r + 1) _).mp present
    have unique := certificate.anchor_unique (extendCoordinates vista (r + 1) y)
      (intrinsic_of_rows vista valid leaders r y hy) (decodeNode vista (r + 1) _)
      ((mem_decodedLevel vista (r + 1) _).mpr ⟨_, info.1, info.2, rfl⟩)
    rwa [extendCoordinates_decode vista valid (r + 1) y j] at unique

/-- Positive integer coordinates used by the actual solver and propagation. -/
def anchorNatural (vista : Vista) (r : Nat) (c : ∀ k, Counting.FullHistory k → Nat) : Array Nat :=
  ((levelNodes vista (r + 1)).map (fun i => c (r + 1) (decodeNode vista (r + 1) i))).toArray

theorem anchorNatural_size (vista : Vista) (r : Nat) (c : ∀ k, Counting.FullHistory k → Nat) :
    (anchorNatural vista r c).size = (levelNodes vista (r + 1)).length := by simp [anchorNatural]

theorem anchorNatural_coordinate (vista : Vista) (r : Nat) (c : ∀ k, Counting.FullHistory k → Nat)
    (j : Fin (levelNodes vista (r + 1)).length) :
    (anchorNatural vista r c)[j.val]?.getD 0 =
      c (r + 1) (decodeNode vista (r + 1) (levelNodes vista (r + 1))[j.val]) := by
  simp [anchorNatural, j.isLt]

theorem anchorNatural_cast (vista : Vista) (r : Nat) (c : ∀ k, Counting.FullHistory k → Nat) :
    vectorArray (fun j : Fin (levelNodes vista (r + 1)).length =>
      (c (r + 1) (decodeNode vista (r + 1) (levelNodes vista (r + 1))[j.val]) : ℚ)) =
      (anchorNatural vista r c).map (fun n : Nat => (n : ℚ)) := by
  simp only [vectorArray, ← List.ofFn_eq_map,
    anchorNatural, List.map_toArray, List.map_map, Function.comp_def]
  apply congrArg List.toArray
  exact List.ofFn_getElem_eq_map _ (fun i => (c (r + 1) (decodeNode vista (r + 1) i) : ℚ))

theorem fullCertificate_natural (vista : Vista) (_valid : vista.valid = true) (leaders candidate last r : Nat)
    (c : ∀ k, Counting.FullHistory k → Nat)
    (certificate : FullCertificate leaders candidate last r (decodedLevel vista) c) :
    positiveNaturals? ((anchorNatural vista r c).map (fun n : Nat => (n : ℚ))) =
      some (anchorNatural vista r c) := by
  apply positiveNaturals_complete
  intro j
  have hj : j.val < (levelNodes vista (r + 1)).length := by
    simpa only [anchorNatural_size] using j.isLt
  have present := (List.getElem_mem hj : (levelNodes vista (r + 1))[j.val] ∈ levelNodes vista (r + 1))
  have info := (mem_levelNodes vista (r + 1) _).mp present
  have positive := certificate.anchor_candidate_positive _
    ((mem_decodedLevel vista (r + 1) _).mpr ⟨_, info.1, info.2, rfl⟩)
  simpa [anchorNatural, hj] using positive

end Counting.Executable
