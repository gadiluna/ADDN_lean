import Counting.ExternalThreeSATGadget
import Counting.ExternalCompletion

namespace Counting.External.ThreeSAT

def variablePartner {n m : ℕ} (assignment : Fin n → Bool) : Equiv.Perm (Slot n m) where
  toFun v := (v.1, if assignment v.1 then v.2 else finRotate (3 * m + 1) v.2)
  invFun v := (v.1, if assignment v.1 then v.2 else (finRotate (3 * m + 1)).symm v.2)
  left_inv := by
    rintro ⟨i, j⟩
    cases h : assignment i <;> simp [h]
  right_inv := by
    rintro ⟨i, j⟩
    cases h : assignment i <;> simp [h]

def assignPorts {n m : ℕ} (assignment : Fin n → Bool) : Slot n m ⊕ Slot n m ≃ Port n m where
  toFun
    | .inl v => (!assignment v.1, v)
    | .inr v => (assignment v.1, v)
  invFun z := if z.1 = assignment z.2.1 then .inr z.2 else .inl z.2
  left_inv := by
    rintro (⟨i, j⟩ | ⟨i, j⟩) <;> cases h : assignment i <;> simp [h]
  right_inv := by
    rintro ⟨bit, i, j⟩
    cases bit <;> cases h : assignment i <;> simp [h]

theorem selected_slots_injective {n m : ℕ} (formula : ThreeSAT n m) (position : Fin m → Fin 3) :
    Function.Injective (fun c => formula.literalSlot c (position c)) := by
  intro a b same
  have occurrenceEq := congrArg Prod.snd same
  exact congrArg Prod.fst (@occurrence_injective m (a, position a) (b, position b) occurrenceEq)

theorem gadget_matching_of_satisfies {n m : ℕ} {formula : ThreeSAT n m}
    (assignment : Fin n → Bool) (satisfies : formula.Satisfies assignment) :
    Nonempty formula.GadgetMatching := by
  classical
  choose position satisfied using satisfies
  obtain ⟨extra, chosen⟩ := exists_completion_equiv
    (fun c => formula.literalSlot c (position c)) (selected_slots_injective formula position)
    (show Fintype.card (Slot n m) = slotCount n m by simp [Slot, slotCount])
  let partner : Equiv.Perm (Place n m) := Equiv.sumCongr (variablePartner assignment) (Equiv.refl _)
  let port : Place n m ≃ Port n m :=
    (Equiv.sumCongr (Equiv.refl _) extra).trans (assignPorts assignment)
  refine ⟨⟨partner, port, ?_⟩⟩
  rintro (v | c | g)
  · change gadgetArc formula (.inl v) (.inl (variablePartner assignment v))
      (assignPorts assignment (.inl v)) = true
    cases ha : assignment v.1 <;>
      simp [gadgetArc, variablePartner, assignPorts, nextSlot, ha]
  · change gadgetArc formula (.inr (.inl c)) (.inr (.inl c))
      (assignPorts assignment (.inr (extra (.inl c)))) = true
    rw [chosen c]
    simp only [gadgetArc, assignPorts, decide_eq_true_eq, true_and]
    refine ⟨position c, ?_⟩
    apply Prod.ext
    · exact beq_iff_eq.mp (satisfied c)
    · rfl
  · change gadgetArc formula (.inr (.inr g)) (.inr (.inr g))
      (assignPorts assignment (.inr (extra (.inr g)))) = true
    simp [gadgetArc]

theorem gadget_matching_iff_yes {n m : ℕ} (formula : ThreeSAT n m) :
    Nonempty formula.GadgetMatching ↔ formula.Yes := by
  refine ⟨gadget_matching_implies_yes, ?_⟩
  rintro ⟨assignment, satisfies⟩
  exact gadget_matching_of_satisfies assignment satisfies

theorem place_card {n m : ℕ} (formula : ThreeSAT n m) :
    Fintype.card (Place n m) = 2 * slotCount n m := by
  have bound := formula.clauses_le_slots
  simp only [Place, Extra, Slot, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  unfold slotCount at bound ⊢
  omega

theorem port_card (n m : ℕ) : Fintype.card (Port n m) = 2 * slotCount n m := by
  simp [Port, Slot, slotCount]

end Counting.External.ThreeSAT
