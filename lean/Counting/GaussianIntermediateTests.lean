import Counting.GaussianIntermediatePhysical

/-! Executable regressions for the actual materialized run, followed by a
kernel-checked application of the general intermediate-bound theorem. -/
namespace Counting.GaussianBits.Tests
open DirectedCounting.VerifiedGaussianAnchorSolver
open RationalSystem

private def swapSystem : RationalSystem 2 :=
  { coeff := fun row col => if row = 0 then (if col = 0 then 0 else 2)
      else (if col = 0 then 3 else 4)
    rhs := fun row => if row = 0 then 4 else 11 }

private def singularSystem : RationalSystem 2 :=
  { coeff := fun row col => if row = 0 then (if col = 0 then 1 else 2)
      else (if col = 0 then 2 else 4)
    rhs := fun row => if row = 0 then 3 else 7 }

private def zeroSystem : RationalSystem 2 := { coeff := 0, rhs := 0 }

private def require (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError label)

private def regressions : IO Unit := do
  let swap := StoredGaussian.runGaussian swapSystem
  require "nonzero pivot found after swap" swap.ok
  require "first operation swaps rows" (decide (swap.opsRev.reverse.head? = some (.swap 0 1)))
  require "exact solution after swaps" (decide (swap.system.rhs 0 = 1 ∧ swap.system.rhs 1 = 2))
  let intermediate :=  StoredGaussian.replay swapSystem (swap.opsRev.reverse.take 2)
  require "normalization creates exact fraction" (decide (intermediate.coeff 0 1 = 4/3))
  let singular := StoredGaussian.runGaussian singularSystem
  require "singular run fails after first completed pivot"
    (decide (singular.ok = false ∧ singular.opsRev.length = 3))
  let zero := StoredGaussian.runGaussian zeroSystem
  require "zero matrix fails before emitting operations" (decide (zero.ok = false ∧ zero.opsRev = []))

#eval regressions

example (length : Nat) (row : Fin 2) (column : Option (Fin 2)) :
    rationalBits (augmented (StoredGaussian.replay singularSystem
      ((StoredGaussian.runGaussian singularSystem).opsRev.reverse.take length)) row column) ≤
      intermediateBound 2 7 := by
  apply storedGaussian_integral_prefix_bits singularSystem 7
  · decide
  · decide

end Counting.GaussianBits.Tests
