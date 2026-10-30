import Counting.ExternalThreeDM

namespace Counting.External

theorem ThreeDM.perfect_unique {q m : ℕ} (I : ThreeDM q m) {chosen : Finset (Fin m)}
    (perfect : I.IsPerfect chosen) (part : Fin 3) {a b : Fin m}
    (ha : a ∈ chosen) (hb : b ∈ chosen) (equal : I.edge a part = I.edge b part) : a = b := by
  obtain ⟨j, single⟩ := Finset.card_eq_one.mp (perfect part (I.edge a part))
  have first : a ∈ chosen.filter (fun k => I.edge k part = I.edge a part) := by simp [ha]
  have second : b ∈ chosen.filter (fun k => I.edge k part = I.edge a part) := by simp [hb, equal]
  rw [single, Finset.mem_singleton] at first second
  exact first.trans second.symm

theorem ThreeDM.perfect_exists {q m : ℕ} (I : ThreeDM q m) {chosen : Finset (Fin m)}
    (perfect : I.IsPerfect chosen) (part : Fin 3) (v : Fin q) :
    ∃ j ∈ chosen, I.edge j part = v := by
  have nonempty : (chosen.filter (fun j => I.edge j part = v)).Nonempty :=
    Finset.card_pos.mp (by rw [perfect part v]; omega)
  obtain ⟨j, hj⟩ := nonempty
  exact ⟨j, (Finset.mem_filter.mp hj).1, (Finset.mem_filter.mp hj).2⟩

noncomputable def ThreeDM.selectedIndex {q m : ℕ} (I : ThreeDM q m) {chosen : Finset (Fin m)}
    (perfect : I.IsPerfect chosen) (v : Fin q) : Fin m :=
  (I.perfect_exists perfect 0 v).choose

theorem ThreeDM.selectedIndex_spec {q m : ℕ} (I : ThreeDM q m) {chosen : Finset (Fin m)}
    (perfect : I.IsPerfect chosen) (v : Fin q) :
    I.selectedIndex perfect v ∈ chosen ∧ I.edge (I.selectedIndex perfect v) 0 = v :=
  (I.perfect_exists perfect 0 v).choose_spec

theorem ThreeDM.selectedIndex_edge {q m : ℕ} (I : ThreeDM q m) {chosen : Finset (Fin m)}
    (perfect : I.IsPerfect chosen) (j : Fin m) (member : j ∈ chosen) :
    I.selectedIndex perfect (I.edge j 0) = j :=
  I.perfect_unique perfect 0 (I.selectedIndex_spec perfect _).1 member
    (I.selectedIndex_spec perfect _).2

noncomputable def ThreeDM.coordinateEquiv {q m : ℕ} (I : ThreeDM q m) {chosen : Finset (Fin m)}
    (perfect : I.IsPerfect chosen) (part : Fin 3) : Equiv.Perm (Fin q) :=
  Equiv.ofBijective (fun v => I.edge (I.selectedIndex perfect v) part) (by
    constructor
    · intro a b equal
      have selectedEq := I.perfect_unique perfect part
        (I.selectedIndex_spec perfect a).1 (I.selectedIndex_spec perfect b).1 equal
      exact (I.selectedIndex_spec perfect a).2.symm.trans
        ((congrArg (fun j => I.edge j 0) selectedEq).trans (I.selectedIndex_spec perfect b).2)
    · intro v
      obtain ⟨j, member, value⟩ := I.perfect_exists perfect part v
      exact ⟨I.edge j 0, by dsimp only; rw [I.selectedIndex_edge perfect j member, value]⟩)

structure FinMatching (q : ℕ) (arc : Fin q → Fin q → Fin q → Bool) where
  partner : Equiv.Perm (Fin q)
  port : Equiv.Perm (Fin q)
  allowed : ∀ x, arc x (partner x) (port x) = true

def tripleEquiv (q : ℕ) : Fin (q * (q * q)) ≃ Fin q × (Fin q × Fin q) :=
  finProdFinEquiv.symm.trans (Equiv.prodCongr (Equiv.refl _) finProdFinEquiv.symm)

def allowedIndices (q : ℕ) (arc : Fin q → Fin q → Fin q → Bool) : Finset (Fin (q * (q * q))) :=
  Finset.univ.filter (fun i => arc (tripleEquiv q i).1 (tripleEquiv q i).2.1 (tripleEquiv q i).2.2)

def graphToThreeDM (q : ℕ) (arc : Fin q → Fin q → Fin q → Bool) :
    ThreeDM q (allowedIndices q arc).card where
  edge j part :=
    let t := tripleEquiv q ((allowedIndices q arc).orderEmbOfFin rfl j)
    if part = 0 then t.1 else if part = 1 then t.2.1 else t.2.2

theorem graphToThreeDM_allowed (q : ℕ) (arc : Fin q → Fin q → Fin q → Bool)
    (j : Fin (allowedIndices q arc).card) :
    arc ((graphToThreeDM q arc).edge j 0) ((graphToThreeDM q arc).edge j 1)
      ((graphToThreeDM q arc).edge j 2) = true := by
  have member := Finset.orderEmbOfFin_mem (allowedIndices q arc) rfl j
  simpa [allowedIndices, graphToThreeDM] using (Finset.mem_filter.mp member).2

theorem graphToThreeDM_sound (q : ℕ) (arc : Fin q → Fin q → Fin q → Bool)
    (yes : (graphToThreeDM q arc).Yes) : Nonempty (FinMatching q arc) := by
  obtain ⟨chosen, perfect⟩ := yes
  let I := graphToThreeDM q arc
  refine ⟨⟨I.coordinateEquiv perfect 1, I.coordinateEquiv perfect 2, ?_⟩⟩
  intro x
  change arc x (I.edge (I.selectedIndex perfect x) 1) (I.edge (I.selectedIndex perfect x) 2) = true
  have allowed := graphToThreeDM_allowed q arc (I.selectedIndex perfect x)
  change arc (I.edge (I.selectedIndex perfect x) 0) (I.edge (I.selectedIndex perfect x) 1)
    (I.edge (I.selectedIndex perfect x) 2) = true at allowed
  rw [(I.selectedIndex_spec perfect x).2] at allowed
  exact allowed

def allowedIndex (q : ℕ) (arc : Fin q → Fin q → Fin q → Bool)
    (x y z : Fin q) (allowed : arc x y z = true) : Fin (allowedIndices q arc).card :=
  ((allowedIndices q arc).orderIsoOfFin rfl).symm
    ⟨(tripleEquiv q).symm (x, y, z), by simp [allowedIndices, allowed]⟩

theorem allowedIndex_coordinates (q : ℕ) (arc : Fin q → Fin q → Fin q → Bool)
    (x y z : Fin q) (allowed : arc x y z = true) (part : Fin 3) :
    (graphToThreeDM q arc).edge (allowedIndex q arc x y z allowed) part =
      if part = 0 then x else if part = 1 then y else z := by
  change (let t := tripleEquiv q (((allowedIndices q arc).orderIsoOfFin rfl)
    (((allowedIndices q arc).orderIsoOfFin rfl).symm
      ⟨(tripleEquiv q).symm (x, y, z), _⟩)).val
    if part = 0 then t.1 else if part = 1 then t.2.1 else t.2.2) = _
  rw [OrderIso.apply_symm_apply, Equiv.apply_symm_apply]

theorem graphToThreeDM_complete (q : ℕ) (arc : Fin q → Fin q → Fin q → Bool)
    (M : FinMatching q arc) : (graphToThreeDM q arc).Yes := by
  let chosenIndex := fun x => allowedIndex q arc x (M.partner x) (M.port x) (M.allowed x)
  let coordinate := fun part : Fin 3 =>
    if part = 0 then Equiv.refl (Fin q) else if part = 1 then M.partner else M.port
  have coordinate_eq : ∀ x part, (graphToThreeDM q arc).edge (chosenIndex x) part = coordinate part x := by
    intro x part
    rw [allowedIndex_coordinates]
    unfold coordinate
    split_ifs <;> rfl
  refine ⟨Finset.univ.image chosenIndex, ?_⟩
  intro part v
  apply Finset.card_eq_one_iff_existsUnique.mpr
  refine ⟨chosenIndex ((coordinate part).symm v), ?_, ?_⟩
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩, ?_⟩
    rw [coordinate_eq, Equiv.apply_symm_apply]
  · intro j hj
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hj).1
    have value := (Finset.mem_filter.mp hj).2
    rw [coordinate_eq] at value
    exact congrArg chosenIndex ((coordinate part).apply_eq_iff_eq_symm_apply.mp value)

theorem graphToThreeDM_iff (q : ℕ) (arc : Fin q → Fin q → Fin q → Bool) :
    (graphToThreeDM q arc).Yes ↔ Nonempty (FinMatching q arc) :=
  ⟨graphToThreeDM_sound q arc, fun ⟨M⟩ => graphToThreeDM_complete q arc M⟩

theorem graphToThreeDM_size (q : ℕ) (arc : Fin q → Fin q → Fin q → Bool) :
    (allowedIndices q arc).card ≤ q ^ 3 := by
  have bound := Finset.card_le_univ (allowedIndices q arc)
  simpa only [Fintype.card_fin, pow_succ, pow_zero, Nat.mul_one, Nat.one_mul, Nat.mul_assoc] using bound

end Counting.External
