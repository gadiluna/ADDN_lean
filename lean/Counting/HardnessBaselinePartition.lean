import Counting.HardnessBaselineGraph

namespace Counting.HardnessBaseline
open DirectedCounting PaperHistory HardnessPath

variable {I : Type} [Fintype I]

theorem member_class_eq_iff (coeff size : I → Nat) (distinct : Function.Injective coeff)
    (B C r : Nat) (weighted : (∑ i, coeff i * size i) = C)
    (positive : 0 < r) (before : r < B) (lengths : ∀ i, r < size i)
    (i j : I) (p : Fin (size i)) (q : Fin (size j)) :
    classOf (network coeff size B) (leader size) r (some ⟨i, p⟩) =
      classOf (network coeff size B) (leader size) r (some ⟨j, q⟩) ↔
        i = j ∧ min p.val r = min q.val r := by
  rw [classOf_eq_iff, ← history_eq_iff_sameMultigraphHistory,
    prefix_history coeff size B r before, prefix_history coeff size B r before]
  exact physical_member_partition coeff size distinct C r weighted positive lengths i j p q

/-- A nonleader class never equals the unique leader class. -/
theorem member_class_ne_leader (coeff size : I → Nat) (B r : Nat) (a : Member size) :
    classOf (network coeff size B) (leader size) r (some a) ≠
      classOf (network coeff size B) (leader size) r none := by
  intro equal
  have labels := congrArg (label (network coeff size B) (leader size) r) equal
  simp only [label_classOf, leader, Bool.false_eq_true] at labels

noncomputable def groupNodes (coeff size : I → Nat) (B r : Nat) (i : I) :
    Finset (Node (network coeff size B) (leader size) r) := by
  classical
  exact Finset.univ.image (fun p : Fin (size i) => classOf (network coeff size B) (leader size) r (some ⟨i, p⟩))

/-- One representative for each singleton position and the terminal suffix. -/
def representative (size : I → Nat) (r : Nat) (lengths : ∀ i, r < size i)
    (i : I) (p : Fin (r+1)) : Fin (size i) := ⟨p.val, by have := lengths i; have := p.isLt; omega⟩

theorem groupNodes_eq_representatives (coeff size : I → Nat) (distinct : Function.Injective coeff)
    (B C r : Nat) (weighted : (∑ i, coeff i * size i) = C)
    (positive : 0 < r) (before : r < B) (lengths : ∀ i, r < size i) (i : I) :
    groupNodes coeff size B r i = Finset.univ.image (fun p : Fin (r+1) =>
      classOf (network coeff size B) (leader size) r (some ⟨i, representative size r lengths i p⟩)) := by
  classical
  ext node
  constructor
  · intro member
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp member
    let q : Fin (r+1) := ⟨min p.val r, by omega⟩
    refine Finset.mem_image.mpr ⟨q, Finset.mem_univ _, ?_⟩
    apply (member_class_eq_iff coeff size distinct B C r weighted positive before lengths _ _ _ _).mpr
    refine ⟨rfl, ?_⟩
    dsimp only [representative, q]
    omega
  · intro member
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp member
    exact Finset.mem_image.mpr ⟨representative size r lengths i p, Finset.mem_univ _, rfl⟩

theorem groupNodes_card (coeff size : I → Nat) (distinct : Function.Injective coeff)
    (B C r : Nat) (weighted : (∑ i, coeff i * size i) = C)
    (positive : 0 < r) (before : r < B) (lengths : ∀ i, r < size i) (i : I) :
    (groupNodes coeff size B r i).card = r+1 := by
  classical
  rw [groupNodes_eq_representatives coeff size distinct B C r weighted positive before lengths i]
  rw [Finset.card_image_iff.mpr]
  · simp
  · intro p _ q _ equal
    have same := (member_class_eq_iff coeff size distinct B C r weighted positive before lengths
      i i (representative size r lengths i p) (representative size r lengths i q)).mp equal
    apply Fin.ext
    dsimp only [representative] at same
    have := p.isLt
    have := q.isLt
    omega

/-- A uniform finite indexing of all history classes at a positive prefix level. -/
noncomputable def classRepresentative (coeff size : I → Nat) (B r : Nat) (lengths : ∀ i, r < size i) :
    Option (I × Fin (r+1)) → Node (network coeff size B) (leader size) r
  | none => classOf (network coeff size B) (leader size) r none
  | some p => classOf (network coeff size B) (leader size) r
      (some ⟨p.1, representative size r lengths p.1 p.2⟩)

theorem classRepresentative_bijective (coeff size : I → Nat) (distinct : Function.Injective coeff)
    (B C r : Nat) (weighted : (∑ i, coeff i * size i) = C)
    (positive : 0 < r) (before : r < B) (lengths : ∀ i, r < size i) :
    Function.Bijective (classRepresentative coeff size B r lengths) := by
  constructor
  · intro a b equal
    cases a with
    | none =>
        cases b with
        | none => rfl
        | some b => exact False.elim (member_class_ne_leader coeff size B r _ equal.symm)
    | some a =>
        cases b with
        | none => exact False.elim (member_class_ne_leader coeff size B r _ equal)
        | some b =>
            obtain ⟨i, p⟩ := a
            obtain ⟨j, q⟩ := b
            have same := (member_class_eq_iff coeff size distinct B C r weighted positive before lengths
              i j (representative size r lengths i p) (representative size r lengths j q)).mp equal
            have group := same.1
            subst j
            congr 2
            apply Fin.ext
            dsimp only [representative] at same
            have := p.isLt
            have := q.isLt
            omega
  · intro node
    have classify : ∀ a : Agent size, ∃ p, classRepresentative coeff size B r lengths p =
        classOf (network coeff size B) (leader size) r a := by
      intro a
      cases a with
      | none => exact ⟨none, rfl⟩
      | some a =>
          obtain ⟨i, p⟩ := a
          let q : Fin (r+1) := ⟨min p.val r, by omega⟩
          refine ⟨some (i, q), ?_⟩
          apply (member_class_eq_iff coeff size distinct B C r weighted positive before lengths _ _ _ _).mpr
          refine ⟨rfl, ?_⟩
          dsimp only [representative, q]
          omega
    obtain ⟨p, equal⟩ := classify node.out
    exact ⟨p, equal.trans (classOf_out _ _ _ node)⟩

theorem prefix_node_card (coeff size : I → Nat) (distinct : Function.Injective coeff)
    (B C r : Nat) (weighted : (∑ i, coeff i * size i) = C)
    (positive : 0 < r) (before : r < B) (lengths : ∀ i, r < size i) :
    Fintype.card (Node (network coeff size B) (leader size) r) = 1 + Fintype.card I * (r+1) := by
  let eqv := Equiv.ofBijective (classRepresentative coeff size B r lengths)
    (classRepresentative_bijective coeff size distinct B C r weighted positive before lengths)
  have cardinal := Fintype.card_congr eqv
  simpa only [Fintype.card_option, Fintype.card_prod, Fintype.card_fin, Nat.add_comm] using cardinal.symm

/-- Every group contributes exactly B nodes to the final visible previous level. -/
theorem final_group_card (coeff size : I → Nat) (distinct : Function.Injective coeff)
    (B C : Nat) (baseLarge : 2 ≤ B) (weighted : (∑ i, coeff i * size i) = C)
    (lengths : ∀ i, B ≤ size i) (i : I) :
    (groupNodes coeff size B (B-1) i).card = B := by
  have card := groupNodes_card coeff size distinct B C (B-1) weighted (by omega) (by omega)
    (fun i => by have := lengths i; omega) i
  omega

end Counting.HardnessBaseline
