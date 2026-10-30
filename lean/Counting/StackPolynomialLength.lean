import Counting.StackUnaryPolynomial
import Counting.StackRoutineUnary

namespace Counting.StackMachine.Routine

abbrev PolynomialWorkspace (extra : Nat) := Fin 6 ↪ Fin (extra+6)

def PolynomialWorkspace.powerRoles (w : PolynomialWorkspace extra) : PowerWorkspace (extra+1) :=
  ⟨fun index => w index.succ, fun _ _ same => Fin.succ_injective 5 (w.injective same)⟩

@[simp] theorem PolynomialWorkspace.powerRoles_apply (w : PolynomialWorkspace extra) (index : Fin 5) :
    w.powerRoles index = w index.succ := rfl

/-- Roles: source, unary base, result, counter, product, scratch. This routine
preserves the source and produces the polynomial of its length. -/
def polynomialLength (extra : Nat) (w : PolynomialWorkspace extra) (coefficient exponent : Nat) : Routine (extra+4) :=
  sequence (ofProgram (Unary.lengthProgram (extra+3) (w 0) (w 1) (w 5)))
    (sequence (pushBit (w 1) true) (monomial (extra+1) w.powerRoles coefficient exponent))

def polynomialLengthTime (length coefficient exponent : Nat) : Nat :=
  5*length+5+monomialTime (length+1) coefficient exponent

theorem polynomialLength_executes (extra : Nat) (w : PolynomialWorkspace extra)
    (coefficient exponent : Nat) (store : Fin (extra+6) → List Bool)
    (baseEmpty : store (w 1) = []) (accEmpty : store (w 2) = [])
    (counterEmpty : store (w 3) = []) (productEmpty : store (w 4) = []) (workEmpty : store (w 5) = []) :
    Executes (polynomialLength extra w coefficient exponent) store
      (polynomialLengthTime (store (w 0)).length coefficient exponent)
      (Function.update (Function.update store (w 1) (List.replicate ((store (w 0)).length+1) true))
        (w 2) (List.replicate (coefficient*((store (w 0)).length+1)^exponent) true)) := by
  let measured := Function.update store (w 1) (List.replicate (store (w 0)).length true)
  have first : Executes (ofProgram (Unary.lengthProgram (extra+3) (w 0) (w 1) (w 5))) store
      (5*(store (w 0)).length+2) measured := by
    obtain ⟨finish,run,halted,finalStore⟩ := length_executes (extra+3) (w 0) (w 1) (w 5)
      (fun same => (by decide : (0 : Fin 6) ≠ 1) (w.injective same))
      (fun same => (by decide : (0 : Fin 6) ≠ 5) (w.injective same))
      (fun same => (by decide : (1 : Fin 6) ≠ 5) (w.injective same)) store workEmpty
    refine ⟨finish,run,halted,?_⟩
    rw [finalStore]
    funext register
    by_cases equal : register = w 1
    · subst register; simp [measured,baseEmpty]
    · simp [measured,Function.update,equal]
      intro same
      exact False.elim (equal same)
  let incremented := Function.update store (w 1) (List.replicate ((store (w 0)).length+1) true)
  have second : Executes (pushBit (w 1) true) measured 1 incremented := by
    simpa only [measured,Function.update_self,Function.update_idem,List.replicate_succ,incremented] using
      pushBit_executes (w 1) true measured
  have third := monomial_executes (extra+1) w.powerRoles ((store (w 0)).length+1) coefficient exponent incremented
    (by simp [incremented,PolynomialWorkspace.powerRoles])
    (by simp [incremented,PolynomialWorkspace.powerRoles,w.injective.eq_iff,accEmpty])
    (by simp [incremented,PolynomialWorkspace.powerRoles,w.injective.eq_iff,counterEmpty])
    (by simp [incremented,PolynomialWorkspace.powerRoles,w.injective.eq_iff,productEmpty])
    (by simp [incremented,PolynomialWorkspace.powerRoles,w.injective.eq_iff,workEmpty])
  have combined := first.sequence (second.sequence third)
  simpa only [Unary.lengthProgram,polynomialLength,polynomialLengthTime,PolynomialWorkspace.powerRoles_apply,incremented,
    show (1 : Fin 5).succ = (2 : Fin 6) from rfl,
    show 5*(store (w 0)).length+2+1+(1+1+monomialTime ((store (w 0)).length+1) coefficient exponent) =
      5*(store (w 0)).length+5+monomialTime ((store (w 0)).length+1) coefficient exponent by omega] using combined

def polynomialLengthCoefficient (coefficient exponent : Nat) : Nat :=
  5+(20*exponent*(coefficient+1)+2*coefficient+1)*2^exponent

/-- A polynomial instruction bound for the concrete length-to-polynomial
routine; the exponent does not depend on the input. -/
theorem polynomialLengthTime_bound (length coefficient exponent : Nat) :
    polynomialLengthTime length coefficient exponent ≤
      polynomialLengthCoefficient coefficient exponent*(length+1)^(exponent+1) := by
  have monomialBound := monomialTime_bound (length+1) coefficient exponent
  have baseBound : (length+1+1)^exponent ≤ 2^exponent*(length+1)^exponent := by
    rw [← mul_pow]
    exact Nat.pow_le_pow_left (by omega) exponent
  have scaled := Nat.mul_le_mul_left (20*exponent*(coefficient+1)+2*coefficient+1) baseBound
  have one : 1 ≤ (length+1)^exponent := Nat.one_le_pow exponent _ (by omega)
  unfold polynomialLengthTime polynomialLengthCoefficient
  rw [pow_succ]
  nlinarith

end Counting.StackMachine.Routine
