import Counting.ExternalCNFCorrectness
import Counting.ExternalThreeSATReduction

namespace Counting.External.CNF

def normalizedX3C {n : ℕ} (formula : CNF n) := formula.toThreeSAT.toThreeDM.toX3C.normalize

/-- Complete executable combinatorial chain from CNF-SAT to normalized
X3C. Cook–Levin and machine-level cost simulation are separate theorems. -/
theorem normalizedX3C_yes_iff {n : ℕ} (formula : CNF n) :
    (∃ chosen, formula.normalizedX3C.IsExactCover chosen) ↔ formula.Satisfiable :=
  formula.toThreeSAT.toX3C_yes_iff.trans formula.toThreeSAT_yes_iff

def variableSizeBound (L : ℕ) := L + L * (L + 1)
def clauseSizeBound (L : ℕ) := L * (3 * L + 2)
def matchingSizeBound (L : ℕ) := 2 * variableSizeBound L * (3 * clauseSizeBound L + 1)

theorem matching_order_bound {n : ℕ} (formula : CNF n) (L : ℕ)
    (varBound : n ≤ L) (clauseBound : formula.length ≤ L) (occurrenceBound : formula.width ≤ L) :
    2 * ThreeSAT.slotCount formula.targetVariables formula.targetClauses ≤ matchingSizeBound L := by
  obtain ⟨nv, nc⟩ := formula.toThreeSAT_size_polynomial L varBound clauseBound occurrenceBound
  unfold ThreeSAT.slotCount matchingSizeBound variableSizeBound clauseSizeBound
  have product := Nat.mul_le_mul nv (show 3 * formula.targetClauses + 1 ≤ 3 * (L * (3 * L + 2)) + 1 by omega)
  nlinarith

/-- Both the explicitly enumerated universe and the number of output
triples have polynomial bounds in the explicit input measure L. -/
theorem normalizedX3C_size_bounds {n : ℕ} (formula : CNF n) (L : ℕ)
    (varBound : n ≤ L) (clauseBound : formula.length ≤ L) (occurrenceBound : formula.width ≤ L) :
    3 * (2 * ThreeSAT.slotCount formula.targetVariables formula.targetClauses + 1 + 1) ≤
        3 * (matchingSizeBound L + 2) ∧
      formula.toThreeSAT.toThreeDM.toX3C.kept.card + 1 + 1 ≤ matchingSizeBound L ^ 3 + 2 := by
  have order := formula.matching_order_bound L varBound clauseBound occurrenceBound
  have edges := graphToThreeDM_size
    (2 * ThreeSAT.slotCount formula.targetVariables formula.targetClauses) formula.toThreeSAT.indexedArc
  have polynomial := Nat.pow_le_pow_left order 3
  have kept := formula.toThreeSAT.toThreeDM.toX3C.kept_card_le
  constructor <;> omega

end Counting.External.CNF
