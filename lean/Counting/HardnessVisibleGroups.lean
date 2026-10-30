import Counting.HardnessVisibleLevels

namespace Counting.HardnessVisible
open DirectedCounting PaperHistory TimingProtocolLocal HardnessPath HardnessBaseline

variable {I : Type} [Fintype I]

theorem blackAncestor_member (coeff : I → Nat) (C r d : Nat) (i : I) (p : Nat) :
    blackAncestor r d (memberHistory coeff C (r+d) i p) = memberHistory coeff C r i p := by
  induction d with
  | zero => rfl
  | succ d ih => exact ih

theorem ancestor_member (coeff : I → Nat) (C r t : Nat) (within : r ≤ t) (i : I) (p : Nat) :
    ancestor r t (memberHistory coeff C t i p) = memberHistory coeff C r i p := by
  have castMember (a b : Nat) (equal : a = b) :
      cast (congrArg FullHistory equal) (memberHistory coeff C a i p) = memberHistory coeff C b i p := by
    cases equal
    rfl
  unfold ancestor
  rw [dif_pos within, castMember t (r+(t-r)) (Nat.add_sub_of_le within).symm]
  exact blackAncestor_member coeff C r (t-r) i p

variable {V : Type} [Fintype V]
variable (G : Nat → V → V → Nat) (leader : V → Bool)
variable {q m : Nat} (inst : X3C.Instance q m)

noncomputable def group (i : Option (Fin m)) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => ∃ p : Fin 2,
    history G leader 1 v = memberHistory inst.coefficient inst.weightedTarget 1 i p.val)

@[simp] theorem mem_group (i : Option (Fin m)) (v : V) :
    v ∈ group G leader inst i ↔ ∃ p : Fin 2,
      history G leader 1 v = memberHistory inst.coefficient inst.weightedTarget 1 i p.val := by
  classical
  simp [group]

theorem group_nonleader (i : Option (Fin m)) (v : V) (member : v ∈ group G leader inst i) :
    leader v = false := by
  obtain ⟨p, equal⟩ := (mem_group G leader inst i v).mp member
  exact congrArg Prod.fst equal

theorem groups_disjoint (large : 2 ≤ q) (i j : Option (Fin m)) (different : i ≠ j) :
    Disjoint (group G leader inst i) (group G leader inst j) := by
  classical
  apply Finset.disjoint_left.mpr
  intro v left right
  obtain ⟨p, first⟩ := (mem_group G leader inst i v).mp left
  obtain ⟨s, second⟩ := (mem_group G leader inst j v).mp right
  exact different ((member_partition inst.coefficient (inst.coefficient_injective large)
    inst.weightedTarget 1 (by omega) i j p.val s.val).mp (first.symm.trans second)).1

theorem last_member_first_group (i : Option (Fin m)) (p : Nat) (v : V)
    (same : history G leader (X3C.base q-1) v =
      memberHistory inst.coefficient inst.weightedTarget (X3C.base q-1) i p) :
    v ∈ group G leader inst i := by
  have earlier := congrArg (ancestor 1 (X3C.base q-1)) same
  rw [ancestor_history G leader 1 _ (by unfold X3C.base; omega),
    ancestor_member _ _ _ _ (by unfold X3C.base; omega)] at earlier
  apply (mem_group G leader inst i v).mpr
  refine ⟨⟨min p 1, by omega⟩, earlier.trans ?_⟩
  apply (member_eq_iff_min _ _ _ _ _ _).mpr
  simp only [min_assoc, min_self]

/-- Each of the B distinct visible descendants has a nonempty full fiber
inside its group's two first-level fibers, in an arbitrary realization. -/
theorem group_lower (observer : V)
    (same : history G leader (X3C.base q) observer = X3CBaseline.leaderView inst)
    (i : Option (Fin m)) : X3C.base q ≤ (group G leader inst i).card := by
  classical
  have witnessed : ∀ p : Fin (X3C.base q), ∃ v : V,
      history G leader (X3C.base q-1) v =
        memberHistory inst.coefficient inst.weightedTarget (X3C.base q-1) i p.val := by
    intro p
    have visible := (baseline_level_mem_iff inst (X3C.base q-1) (by unfold X3C.base; omega)
      (memberHistory inst.coefficient inst.weightedTarget (X3C.base q-1) i p.val)).mpr
        (Or.inr ⟨i, ⟨p.val, by have := p.isLt; unfold X3C.base at *; omega⟩, rfl⟩)
    rw [← same, ← represented_histories G leader (X3C.base q) observer (X3C.base q-1) (by omega)] at visible
    obtain ⟨v, _, history⟩ := Finset.mem_image.mp visible
    exact ⟨v, history⟩
  choose representative histories using witnessed
  let selected (p : Fin (X3C.base q)) : ↥(group G leader inst i) :=
    ⟨representative p, last_member_first_group G leader inst i p.val _ (histories p)⟩
  have injective : Function.Injective selected := by
    intro p s equal
    have agents := congrArg Subtype.val equal
    have historiesEqual := (histories p).symm.trans ((congrArg (history G leader (X3C.base q-1)) agents).trans (histories s))
    have positions := (member_eq_iff_min inst.coefficient inst.weightedTarget (X3C.base q-1) i p.val s.val).mp historiesEqual
    apply Fin.ext
    have pbound := p.isLt
    have sbound := s.isLt
    unfold X3C.base at *
    omega
  have count := Fintype.card_le_of_injective selected injective
  simpa only [Fintype.card_fin, Fintype.card_coe] using count

end Counting.HardnessVisible
