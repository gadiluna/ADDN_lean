import Counting.ExternalThreeSATMatching
import Counting.ExternalMatching

namespace Counting.External.ThreeSAT

def placeEquiv {n m : ℕ} (formula : ThreeSAT n m) :
    Place n m ≃ Fin (2 * slotCount n m) := by
  let slots : Slot n m ≃ Fin (slotCount n m) := finProdFinEquiv
  let extra : Extra n m ≃ Fin (slotCount n m) :=
    finSumFinEquiv.trans (finCongr (by have := formula.clauses_le_slots; omega))
  exact ((Equiv.sumCongr slots extra).trans finSumFinEquiv).trans (finCongr (by omega))

def portEquiv (n m : ℕ) : Port n m ≃ Fin (2 * slotCount n m) :=
  (Equiv.prodCongr finTwoEquiv.symm finProdFinEquiv).trans finProdFinEquiv

def indexedArc {n m : ℕ} (formula : ThreeSAT n m) :
    Fin (2 * slotCount n m) → Fin (2 * slotCount n m) → Fin (2 * slotCount n m) → Bool :=
  fun x y z => formula.gadgetArc (formula.placeEquiv.symm x)
    (formula.placeEquiv.symm y) ((portEquiv n m).symm z)

def GadgetMatching.toFinMatching {n m : ℕ} {formula : ThreeSAT n m}
    (M : formula.GadgetMatching) : FinMatching (2 * slotCount n m) formula.indexedArc where
  partner := formula.placeEquiv.symm.trans (M.partner.trans formula.placeEquiv)
  port := formula.placeEquiv.symm.trans (M.port.trans (portEquiv n m))
  allowed := by
    intro x
    simpa only [indexedArc, Equiv.trans_apply, Equiv.symm_apply_apply] using
      M.allowed (formula.placeEquiv.symm x)

def fromFinMatching {n m : ℕ} (formula : ThreeSAT n m)
    (M : FinMatching (2 * slotCount n m) formula.indexedArc) : formula.GadgetMatching where
  partner := formula.placeEquiv.trans (M.partner.trans formula.placeEquiv.symm)
  port := formula.placeEquiv.trans (M.port.trans (portEquiv n m).symm)
  allowed := by
    intro x
    simpa only [indexedArc, Equiv.trans_apply, Equiv.symm_apply_apply] using
      M.allowed (formula.placeEquiv x)

theorem indexed_matching_iff {n m : ℕ} (formula : ThreeSAT n m) :
    Nonempty (FinMatching (2 * slotCount n m) formula.indexedArc) ↔
      Nonempty formula.GadgetMatching :=
  ⟨fun ⟨M⟩ => ⟨formula.fromFinMatching M⟩, fun ⟨M⟩ => ⟨M.toFinMatching⟩⟩

/-- Enumerate only allowed triples in the finite q³ box. This executable
construction uses explicit finite universes throughout. -/
def toThreeDM {n m : ℕ} (formula : ThreeSAT n m) :
    ThreeDM (2 * slotCount n m) (allowedIndices (2 * slotCount n m) formula.indexedArc).card :=
  graphToThreeDM (2 * slotCount n m) formula.indexedArc

theorem toThreeDM_yes_iff {n m : ℕ} (formula : ThreeSAT n m) :
    formula.toThreeDM.Yes ↔ formula.Yes :=
  (graphToThreeDM_iff _ _).trans (formula.indexed_matching_iff.trans formula.gadget_matching_iff_yes)

theorem toThreeDM_size {n m : ℕ} (formula : ThreeSAT n m) :
    (allowedIndices (2 * slotCount n m) formula.indexedArc).card ≤ (2 * n * (3 * m + 1)) ^ 3 := by
  simpa only [slotCount, Nat.mul_assoc] using graphToThreeDM_size (2 * slotCount n m) formula.indexedArc

theorem toThreeDM_size_polynomial {n m : ℕ} (formula : ThreeSAT n m) (L : ℕ)
    (varBound : n ≤ L) (clauses : m ≤ L) :
    2 * slotCount n m ≤ 2 * L * (3 * L + 1) ∧
      (allowedIndices (2 * slotCount n m) formula.indexedArc).card ≤ (2 * L * (3 * L + 1)) ^ 3 := by
  have vertices : 2 * slotCount n m ≤ 2 * L * (3 * L + 1) := by
    unfold slotCount
    have product := Nat.mul_le_mul varBound (show 3 * m + 1 ≤ 3 * L + 1 by omega)
    nlinarith
  exact ⟨vertices, (graphToThreeDM_size _ _).trans (Nat.pow_le_pow_left vertices 3)⟩

/-- Composed yes/no equivalence through normalized X3C; this does not
assert NP-completeness or a Turing-machine running-time bound. -/
theorem toX3C_yes_iff {n m : ℕ} (formula : ThreeSAT n m) :
    (∃ chosen, formula.toThreeDM.toX3C.normalize.IsExactCover chosen) ↔ formula.Yes :=
  formula.toThreeDM.toNormalizedX3C_yes_iff.trans formula.toThreeDM_yes_iff

end Counting.External.ThreeSAT
