import Counting.StackRealizabilityVistaParser

namespace Counting.StackMachine.VistaComplement
open EncodingPrograms

/-- A common bound for the six canonical field readers. These constants
are determined by the concrete parser combinators, not assumed runtimes. -/
theorem fieldReaderCost_le (coefficient exponent source piece total : Nat)
    (coefficientBound : coefficient ≤ 4000) (exponentBound : exponent ≤ 4)
    (sourceBound : source ≤ total) (pieceBound : piece ≤ total) :
    Complexity.polynomial coefficient exponent source+2*piece+2 ≤ 4002*(total+1)^4 := by
  have positive : 1 ≤ total+1 := by omega
  have power : (source+1)^exponent ≤ (total+1)^4 :=
    (Nat.pow_le_pow_left (by omega) exponent).trans (Nat.pow_le_pow_right positive exponentBound)
  have product := Nat.mul_le_mul coefficientBound power
  have linear : total+1 ≤ (total+1)^4 := Nat.le_self_pow (by decide) _
  unfold Complexity.polynomial
  omega

theorem vistaParser_coefficient : DagParser.vista.coefficient ≤ 4000 := by decide
theorem vistaParser_degree : DagParser.vista.exponent ≤ 4 := by decide
theorem naturalParser_coefficient : DagParser.natural.coefficient ≤ 4000 := by decide
theorem naturalParser_degree : DagParser.natural.exponent ≤ 4 := by decide
theorem naturalsParser_coefficient : DagParser.naturals.coefficient ≤ 4000 := by decide
theorem naturalsParser_degree : DagParser.naturals.exponent ≤ 4 := by decide

end Counting.StackMachine.VistaComplement
