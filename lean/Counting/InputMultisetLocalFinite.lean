import Counting.InputMultisetLocal

namespace Counting.InputMultisetLocal
open scoped BigOperators

variable {Input : Type} [DecidableEq Input]

@[simp] theorem weightAt_mem {r : Nat} (s : Finset (InputProtocol.FullHistory Input r))
    (w : ∀ h ∈ s, Nat) (h : InputProtocol.FullHistory Input r) (hh : h ∈ s) :
    weightAt s w h = w h hh := by simp [weightAt, hh]

theorem reconstruction_eq_of_certificates (n t : Nat)
    (H : InputProtocol.FullHistory Input t) (answer : Multiset Input)
    (sound : ∀ r ∈ Finset.range (n - 1),
      ∀ w ∈ solutions n r (levels t H (r + 1)),
        candidateOutput r (levels t H (r + 1)) w = answer)
    (complete : ∃ r ∈ Finset.range (n - 1),
      ∃ w ∈ solutions n r (levels t H (r + 1)),
        candidateOutput r (levels t H (r + 1)) w = answer) :
    reconstruction n t H = answer := by
  apply le_antisymm
  · apply Finset.sup_le
    intro r hr
    apply Finset.sup_le
    intro w hw
    exact le_of_eq (sound r hr w hw)
  · obtain ⟨r, hr, w, hw, hout⟩ := complete
    apply Finset.le_sup_of_le hr
    apply Finset.le_sup_of_le hw
    exact le_of_eq hout.symm

end Counting.InputMultisetLocal
