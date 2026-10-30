import Counting.LowerSeveralInitialGraph
import Counting.LowerSeveralTimeline
import Counting.LowerSeveralFinal

/-!
# The complete multi-leader network schedule

The parameters are `ell = k+2` and `n = k+g+3`. Initial delay occupies
rounds 1 through g; each middle phase lasts k+1 rounds; the fixed final
Hamiltonian cycle is then repeated forever. All labels are the leader labels
of `LowerSeveralRelay`, including at the arbitrary number g of relays.
-/

namespace Counting.LowerSeveral
open LowerSeveralPhases

def smallNetwork (k g round : Nat) : Small k g → Small k g → Nat :=
  if round ≤ g then LowerSeveralInitial.initialSmall k g
  else if round ≤ g + (k + 1) then firstSmall k g
  else if hs : round ≤ g + (k + 1) + (k + 1) then
    secondSmall k g ⟨round - (g + (k + 1)) - 1, by omega⟩
  else LowerSeveralFinal.smallGraph k g

def largeNetwork (k g round : Nat) : Large k g → Large k g → Nat :=
  if round ≤ g then LowerSeveralInitial.initialLarge k g
  else if hf : round ≤ g + (k + 1) then
    firstLarge k g ⟨round - g - 1, by omega⟩
  else if hs : round ≤ g + (k + 1) + (k + 1) then
    secondLarge k g ⟨round - (g + (k + 1)) - 1, by omega⟩
  else LowerSeveralFinal.largeGraph k g

theorem small_initial_round (k g t : Nat) (ht : t ≤ g) :
    smallNetwork k g t = LowerSeveralInitial.initialSmall k g := by
  simp only [smallNetwork, if_pos ht]

theorem large_initial_round (k g t : Nat) (ht : t ≤ g) :
    largeNetwork k g t = LowerSeveralInitial.initialLarge k g := by
  simp only [largeNetwork, if_pos ht]

theorem small_first_round (k g t : Nat) (ht : t < k + 1) :
    smallNetwork k g (g + t + 1) = firstSmall k g := by
  simp only [smallNetwork, if_neg (show ¬g + t + 1 ≤ g by omega),
    if_pos (show g + t + 1 ≤ g + (k + 1) by omega)]

theorem large_first_round (k g t : Nat) (ht : t < k + 1) :
    largeNetwork k g (g + t + 1) = firstLarge k g ⟨t, by omega⟩ := by
  simp only [largeNetwork, if_neg (show ¬g + t + 1 ≤ g by omega),
    dif_pos (show g + t + 1 ≤ g + (k + 1) by omega)]
  congr 1
  apply Fin.ext
  change g + t + 1 - g - 1 = t
  omega

theorem small_second_round (k g t : Nat) (ht : t < k + 1) :
    smallNetwork k g (g + (k + 1) + t + 1) = secondSmall k g ⟨t, by omega⟩ := by
  simp only [smallNetwork, if_neg (show ¬g + (k + 1) + t + 1 ≤ g by omega),
    if_neg (show ¬g + (k + 1) + t + 1 ≤ g + (k + 1) by omega),
    dif_pos (show g + (k + 1) + t + 1 ≤ g + (k + 1) + (k + 1) by omega)]
  congr 1
  apply Fin.ext
  change g + (k + 1) + t + 1 - (g + (k + 1)) - 1 = t
  omega

theorem large_second_round (k g t : Nat) (ht : t < k + 1) :
    largeNetwork k g (g + (k + 1) + t + 1) = secondLarge k g ⟨t, by omega⟩ := by
  simp only [largeNetwork, if_neg (show ¬g + (k + 1) + t + 1 ≤ g by omega),
    dif_neg (show ¬g + (k + 1) + t + 1 ≤ g + (k + 1) by omega),
    dif_pos (show g + (k + 1) + t + 1 ≤ g + (k + 1) + (k + 1) by omega)]
  congr 1
  apply Fin.ext
  change g + (k + 1) + t + 1 - (g + (k + 1)) - 1 = t
  omega

theorem small_final_round (k g t : Nat) :
    smallNetwork k g (g + (k + 1) + (k + 1) + t + 1) =
      LowerSeveralFinal.smallGraph k g := by
  simp only [smallNetwork,
    if_neg (show ¬g + (k + 1) + (k + 1) + t + 1 ≤ g by omega),
    if_neg (show ¬g + (k + 1) + (k + 1) + t + 1 ≤ g + (k + 1) by omega),
    dif_neg (show ¬g + (k + 1) + (k + 1) + t + 1 ≤ g + (k + 1) + (k + 1) by omega)]

theorem large_final_round (k g t : Nat) :
    largeNetwork k g (g + (k + 1) + (k + 1) + t + 1) =
      LowerSeveralFinal.largeGraph k g := by
  simp only [largeNetwork,
    if_neg (show ¬g + (k + 1) + (k + 1) + t + 1 ≤ g by omega),
    dif_neg (show ¬g + (k + 1) + (k + 1) + t + 1 ≤ g + (k + 1) by omega),
    dif_neg (show ¬g + (k + 1) + (k + 1) + t + 1 ≤ g + (k + 1) + (k + 1) by omega)]

theorem small_valid (k g t : Nat) : RoundValid (smallNetwork k g t) (k + 2) := by
  unfold smallNetwork
  split_ifs
  · exact LowerSeveralInitial.initialSmall_valid k g
  · exact firstSmall_valid k g
  · exact secondSmall_valid k g _
  · exact LowerSeveralFinal.smallGraph_valid k g

theorem large_valid (k g t : Nat) : RoundValid (largeNetwork k g t) (k + 2) := by
  unfold largeNetwork
  split_ifs
  · exact LowerSeveralInitial.initialLarge_valid k g
  · exact firstLarge_valid k g _
  · exact secondLarge_valid k g _
  · exact LowerSeveralFinal.largeGraph_valid k g

@[simp] theorem small_order (k g : Nat) : Fintype.card (Small k g) = k + g + 3 := by
  simp [LowerSeveralPhases.Small, LowerSeveralRelay.Vertex, LowerSeveralRelay.Core, Leaders]
  omega

@[simp] theorem large_order (k g : Nat) : Fintype.card (Large k g) = 2 * (k + 2) + g := by
  simp [Large, LowerSeveralRelay.Vertex, LowerSeveralRelay.Core, Leaders]
  omega

theorem different_orders (k g : Nat) : Fintype.card (Small k g) ≠ Fintype.card (Large k g) := by
  rw [small_order, large_order]
  omega

theorem small_admissible (k g : Nat) :
    Admissible (k + 2) (smallNetwork k g) LowerSeveralRelay.leader where
  positive := by omega
  leaders := by simpa only [Leaders, Fintype.card_fin] using
    (LowerSeveralRelay.leader_count (L := Leaders k) (N := Unit) g)
  connected := fun t _ => (small_valid k g t).connected

theorem large_admissible (k g : Nat) :
    Admissible (k + 2) (largeNetwork k g) LowerSeveralRelay.leader where
  positive := by omega
  leaders := by simpa only [Leaders, Fintype.card_fin] using
    (LowerSeveralRelay.leader_count (L := Leaders k) (N := Leaders k) g)
  connected := fun t _ => (large_valid k g t).connected

end Counting.LowerSeveral
