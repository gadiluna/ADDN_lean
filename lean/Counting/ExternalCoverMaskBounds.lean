import Counting.ExternalCoverMaskSemantics

namespace Counting.External.CoverVerification

theorem hits_le_rows (rows : List (List Nat)) (mask : List Bool) (element : Nat) :
    hits rows mask element ≤ rows.length := by
  induction rows generalizing mask with
  | nil => simp [hits]
  | cons row rows ih =>
    cases mask with
    | nil => simp [hits]
    | cons bit mask =>
      have tail := ih mask
      simp only [hits,List.length_cons]
      split <;> omega

@[simp] theorem singleton_counter (count : Nat) :
    (List.replicate count true=[true]) ↔ count=1 := by
  constructor
  · intro equal
    have lengths := congrArg List.length equal
    simpa using lengths
  · rintro rfl;rfl

end Counting.External.CoverVerification
