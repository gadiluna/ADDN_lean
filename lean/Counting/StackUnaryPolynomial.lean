import Counting.StackUnaryPower

namespace Counting.StackMachine.Routine

/-- Evaluate a fixed-coefficient, fixed-exponent monomial on an existing
unary base. The coefficient is emitted by a finite sequence of pushes. -/
def monomial (extra : Nat) (w : PowerWorkspace extra) (coefficient exponent : Nat) : Routine (extra+3) :=
  sequence (prepend (w 1) (List.replicate coefficient true)) (power extra w exponent)

def monomialTime (base coefficient exponent : Nat) : Nat :=
  2*coefficient+1+powerTime base coefficient exponent

theorem monomial_executes (extra : Nat) (w : PowerWorkspace extra)
    (base coefficient exponent : Nat) (store : Fin (extra+5) → List Bool)
    (baseValue : store (w 0) = List.replicate base true)
    (accEmpty : store (w 1) = []) (counterEmpty : store (w 2) = [])
    (productEmpty : store (w 3) = []) (workEmpty : store (w 4) = []) :
    Executes (monomial extra w coefficient exponent) store (monomialTime base coefficient exponent)
      (Function.update store (w 1) (List.replicate (coefficient*base^exponent) true)) := by
  let initialized := Function.update store (w 1) (List.replicate coefficient true)
  have init : Executes (prepend (w 1) (List.replicate coefficient true)) store
      (2*coefficient) initialized := by
    simpa only [accEmpty,List.append_nil,List.length_replicate,initialized] using
      prepend_executes (w 1) (List.replicate coefficient true) store
  have measured := power_executes extra w exponent initialized base coefficient
    (by simp [initialized,w.injective.eq_iff,baseValue]) (by simp [initialized])
    (by simp [initialized,w.injective.eq_iff,counterEmpty])
    (by simp [initialized,w.injective.eq_iff,productEmpty])
    (by simp [initialized,w.injective.eq_iff,workEmpty])
  have combined := init.sequence measured
  simpa only [monomial,monomialTime,initialized,Function.update_idem] using combined

/-- Coefficients and exponents belong to the compiled program; the base is
runtime data. This bound charges every loop and every connecting jump. -/
theorem monomialTime_bound (base coefficient exponent : Nat) :
    monomialTime base coefficient exponent ≤
      (20*exponent*(coefficient+1)+2*coefficient+1)*(base+1)^exponent := by
  have bounded := powerTime_bound base coefficient exponent
  have one : 1 ≤ (base+1)^exponent := Nat.one_le_pow exponent _ (by omega)
  have constant := Nat.mul_le_mul_left (2*coefficient+1) one
  unfold monomialTime
  nlinarith

end Counting.StackMachine.Routine
