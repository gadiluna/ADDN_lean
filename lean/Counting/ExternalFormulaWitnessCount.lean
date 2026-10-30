import Counting.ExternalFormulaCount

namespace Counting.External.CookLevin.StackGenerator
open InitialRows

theorem initialKind_witness_iff (place offset : Nat) (header : List Bool) (capacity : Nat) :
    initialKind place offset header capacity = .witness ↔
      offset+header.length ≤ place ∧ place < offset+header.length+capacity := by
  by_cases after : offset ≤ place
  · rw [initialKind,if_pos after]
    cases found : header[place-offset]? with
    | some bit =>
        have inside := (List.getElem?_eq_some_iff.mp found).1
        cases bit <;> simp only [bitKind,Bool.false_eq_true,ite_false,ite_true]
        all_goals constructor
        all_goals solve | intro impossible; cases impossible | intro bounds; omega
    | none =>
        have outside := List.getElem?_eq_none_iff.mp found
        by_cases past : header.length+capacity ≤ place-offset
        · rw [if_pos past]
          constructor
          · intro impossible; cases impossible
          · intro bounds; omega
        · rw [if_neg past]
          constructor
          · intro _; constructor <;> omega
          · intro _; rfl
  · rw [initialKind,if_neg after]
    constructor
    · intro impossible; cases impossible
    · intro bounds; omega

def witnessPlaceEquiv {width : Nat} (setup : Setup width) :
    {place : Fin width // initialKind place.val setup.offset.val setup.header setup.capacity = .witness} ≃
      Fin setup.capacity where
  toFun place := ⟨place.val.val-(setup.offset.val+setup.header.length),by
    have bounds := (initialKind_witness_iff _ _ _ _).mp place.property
    omega⟩
  invFun position := ⟨setup.witnessIndex position,by
    apply (initialKind_witness_iff _ _ _ _).mpr
    have bounded := position.isLt
    simp only [Setup.witnessIndex]
    constructor <;> omega⟩
  left_inv place := by
    apply Subtype.ext
    apply Fin.ext
    have bounds := (initialKind_witness_iff _ _ _ _).mp place.property
    simp only [Setup.witnessIndex]
    omega
  right_inv position := by
    apply Fin.ext
    simp only [Setup.witnessIndex]
    omega

theorem initialKind_witness_count {width : Nat} (setup : Setup width) :
    ((List.finRange width).filter (fun place =>
      initialKind place.val setup.offset.val setup.header setup.capacity = .witness)).length = setup.capacity := by
  rw [finRange_filter_card]
  simpa only [decide_eq_true_eq,Fintype.card_fin] using Fintype.card_congr (witnessPlaceEquiv setup)

end Counting.External.CookLevin.StackGenerator
