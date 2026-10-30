import Counting.X3CDeduplicate
import Mathlib.Logic.Equiv.Fin.Basic

namespace Counting.External

/-- Explicit three-dimensional matching input. Each edge has one vertex
in each of three disjoint copies of Fin q; duplicate edges are permitted. -/
structure ThreeDM (q m : ℕ) where
  edge : Fin m → Fin 3 → Fin q

def ThreeDM.IsPerfect {q m : ℕ} (I : ThreeDM q m) (chosen : Finset (Fin m)) : Prop :=
  ∀ part : Fin 3, ∀ v : Fin q, (chosen.filter (fun j => I.edge j part = v)).card = 1

def ThreeDM.Yes {q m : ℕ} (I : ThreeDM q m) : Prop := ∃ chosen, I.IsPerfect chosen

/-- Tag the three parts in a single explicit universe of size 3q. -/
def ThreeDM.element {q : ℕ} (part : Fin 3) (v : Fin q) : Fin (3 * q) :=
  finProdFinEquiv (part, v)

theorem ThreeDM.element_injective {q : ℕ} :
    Function.Injective (fun p : Fin 3 × Fin q => ThreeDM.element p.1 p.2) :=
  finProdFinEquiv.injective

def ThreeDM.toX3C {q m : ℕ} (I : ThreeDM q m) : X3C.RawInstance q m where
  triples j := Finset.univ.image (fun part => ThreeDM.element part (I.edge j part))
  triple_card j := by
    rw [Finset.card_image_of_injective]
    · exact Fintype.card_fin 3
    · intro a b same
      exact congrArg Prod.fst (finProdFinEquiv.injective same)

theorem ThreeDM.mem_toX3C {q m : ℕ} (I : ThreeDM q m)
    (part : Fin 3) (v : Fin q) (j : Fin m) :
    ThreeDM.element part v ∈ I.toX3C.triples j ↔ I.edge j part = v := by
  simp only [toX3C, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, equal⟩
    have pairEq := finProdFinEquiv.injective equal
    have partEq := congrArg Prod.fst pairEq
    change a = part at partEq
    subst a
    exact congrArg Prod.snd pairEq
  · intro equal
    exact ⟨part, congrArg (ThreeDM.element part) equal⟩

theorem ThreeDM.perfect_iff_exactCover {q m : ℕ} (I : ThreeDM q m)
    (chosen : Finset (Fin m)) : I.IsPerfect chosen ↔ I.toX3C.IsExactCover chosen := by
  constructor
  · intro perfect e
    obtain ⟨⟨part, v⟩, rfl⟩ := finProdFinEquiv.surjective e
    change (chosen.filter (fun j => ThreeDM.element part v ∈ I.toX3C.triples j)).card = 1
    simpa only [I.mem_toX3C] using perfect part v
  · intro cover part v
    simpa only [I.mem_toX3C] using cover (ThreeDM.element part v)

/-- The reduction keeps the edge index set exactly and introduces no
implicit universe: its output has 3q explicit elements and m triples. -/
theorem ThreeDM.toX3C_yes_iff {q m : ℕ} (I : ThreeDM q m) :
    (∃ chosen, I.toX3C.IsExactCover chosen) ↔ I.Yes := by
  exact exists_congr (fun chosen => (I.perfect_iff_exactCover chosen).symm)

theorem ThreeDM.toNormalizedX3C_yes_iff {q m : ℕ} (I : ThreeDM q m) :
    (∃ chosen, I.toX3C.normalize.IsExactCover chosen) ↔ I.Yes :=
  I.toX3C.normalize_exactCover_iff.trans I.toX3C_yes_iff

theorem ThreeDM.normalized_size {q m : ℕ} (I : ThreeDM q m) :
    2 ≤ q + 1 + 1 ∧ I.toX3C.kept.card + 1 + 1 ≤ m + 2 :=
  I.toX3C.normalize_parameters

theorem ThreeDM.perfect_card {q m : ℕ} (I : ThreeDM q m) (chosen : Finset (Fin m))
    (perfect : I.IsPerfect chosen) : chosen.card = q := by
  have cover := (I.perfect_iff_exactCover chosen).mp perfect
  have reduced := I.toX3C.deduplicate_cover chosen cover
  have cardDedup := X3C.Instance.IsExactCover.card_eq I.toX3C.deduplicate reduced
  have injective : Set.InjOn I.toX3C.toDeduplicated chosen := by
    intro a ha b hb equal
    apply I.toX3C.cover_injective chosen cover ha hb
    simpa only [I.toX3C.toDeduplicated_triple] using congrArg I.toX3C.deduplicate.triples equal
  rw [Finset.card_image_of_injOn injective] at cardDedup
  exact cardDedup

end Counting.External
