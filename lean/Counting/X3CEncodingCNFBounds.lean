import Counting.X3CEncodingCNF

namespace Counting.X3CEncoding.CNFReduction
open External

theorem matchingSizeBound_polynomial (L : Nat) : CNF.matchingSizeBound L ≤ 40*(L+1)^4 := by
  have positive : 1 ≤ (L+1)^2 := Nat.one_le_pow 2 _ (by omega)
  have vars : CNF.variableSizeBound L ≤ 2*(L+1)^2 := by
    unfold CNF.variableSizeBound
    nlinarith
  have clauses : CNF.clauseSizeBound L ≤ 3*(L+1)^2 := by
    unfold CNF.clauseSizeBound
    nlinarith
  have slots : 3*CNF.clauseSizeBound L+1 ≤ 10*(L+1)^2 := by omega
  calc
    CNF.matchingSizeBound L = 2*CNF.variableSizeBound L*(3*CNF.clauseSizeBound L+1) := rfl
    _ ≤ 2*(2*(L+1)^2)*(10*(L+1)^2) := Nat.mul_le_mul (Nat.mul_le_mul_left 2 vars) slots
    _ = 40*(L+1)^4 := by ring

theorem sizeBound_polynomial (L : Nat) : sizeBound L ≤ 30*(40+40^3+1)^2*(L+1)^24 := by
  have matching := matchingSizeBound_polynomial L
  have positive : 1 ≤ L+1 := by omega
  have power : (L+1)^4 ≤ (L+1)^12 := Nat.pow_le_pow_right positive (by omega)
  have first := matching.trans (Nat.mul_le_mul_left 40 power)
  have cube : (CNF.matchingSizeBound L)^3 ≤ 40^3*(L+1)^12 := by
    have cubed := Nat.pow_le_pow_left matching 3
    simpa only [mul_pow, ← pow_mul] using cubed
  have unit : 1 ≤ (L+1)^12 := Nat.one_le_pow 12 _ positive
  have sum : CNF.matchingSizeBound L+(CNF.matchingSizeBound L)^3+1 ≤
      (40+40^3+1)*(L+1)^12 := by omega
  have square := Nat.mul_le_mul_left 30 (Nat.pow_le_pow_left sum 2)
  simpa only [sizeBound, mul_pow, ← pow_mul, Nat.mul_assoc] using square

theorem noInstance_length : (codec.encode noInstance).length = 9 := by decide

def reductionSizeCoefficient : Nat := 30*(40+40^3+1)^2+9

/-- Polynomial output-size bound for the total binary reduction, measured
in the number of bits of the encoded input and output. -/
theorem reduce_length_polynomial (word : List Bool) :
    (reduce word).length ≤ Complexity.polynomial reductionSizeCoefficient 24 word.length := by
  have raw := reduce_length word
  rw [noInstance_length] at raw
  have main := sizeBound_polynomial word.length
  have positive : 1 ≤ (word.length+1)^24 := Nat.one_le_pow 24 _ (by omega)
  unfold Complexity.polynomial reductionSizeCoefficient
  nlinarith

end Counting.X3CEncoding.CNFReduction
