import Counting.StackEmitTemplates

namespace Counting.StackMachine.Routine

/-- Emit the natural codec of a fixed multiple of a runtime unary length. -/
def emitScaledNatural (extra : Nat) (w : PolynomialWorkspace extra) (scale : Nat) : Routine (extra+4) :=
  sequence (scaleLength (extra+3) (w 0) (w 1) (w 5) scale)
    (sequence (emitNatural (extra+1) w.powerRoles) (clear (w 1)))

def emitScaledNaturalCoefficient (scale : Nat) := 20*(scale+1)^2+6*scale+6

theorem emitScaledNatural_executes (extra : Nat) (w : PolynomialWorkspace extra) (scale : Nat)
    (store : Fin (extra+6) → List Bool) (baseEmpty : store (w 1)=[])
    (counterEmpty : store (w 3)=[]) (binaryEmpty : store (w 4)=[]) (workEmpty : store (w 5)=[]) :
    ∃ transitions ≤ emitScaledNaturalCoefficient scale*((store (w 0)).length+1)^2,
      Executes (emitScaledNatural extra w scale) store transitions
        (Function.update store (w 2) (Encoding.natural.encode (scale*(store (w 0)).length)++store (w 2))) := by
  have distinct {a b : Fin 6} (different : a ≠ b) : w a ≠ w b := fun same => different (w.injective same)
  let measured := Function.update store (w 1) (List.replicate (scale*(store (w 0)).length) true)
  have measurement : Executes (scaleLength (extra+3) (w 0) (w 1) (w 5) scale) store
      (scale*(5*(store (w 0)).length+3)) measured := by
    simpa only [baseEmpty,List.append_nil,measured] using
      scaleLength_executes (extra+3) (w 0) (w 1) (w 5)
        (distinct (by decide)) (distinct (by decide)) (distinct (by decide)) scale store workEmpty
  obtain ⟨emitTime,emitBound,emitted⟩ := emitNatural_executes (extra+1) w.powerRoles measured
    (by simp [measured,PolynomialWorkspace.powerRoles,w.injective.eq_iff,counterEmpty])
    (by simp [measured,PolynomialWorkspace.powerRoles,w.injective.eq_iff,binaryEmpty])
    (by simp [measured,PolynomialWorkspace.powerRoles,w.injective.eq_iff,workEmpty])
  let payload := Encoding.natural.encode (scale*(store (w 0)).length)++store (w 2)
  let afterEmit := Function.update measured (w 2) payload
  have emission : Executes (emitNatural (extra+1) w.powerRoles) measured emitTime afterEmit := by
    simpa [PolynomialWorkspace.powerRoles,measured,afterEmit,payload,w.injective.eq_iff] using emitted
  have clearing := clear_executes (w 1) afterEmit
  have measuredBase : afterEmit (w 1)=List.replicate (scale*(store (w 0)).length) true := by
    simp [afterEmit,measured,w.injective.eq_iff]
  have finalStore : Function.update afterEmit (w 1) []=Function.update store (w 2) payload := by
    funext r
    by_cases base : r=w 1
    · subst r; simp [w.injective.eq_iff,baseEmpty]
    · by_cases output : r=w 2
      · subst r; simp [afterEmit,w.injective.eq_iff]
      · simp [afterEmit,measured,base,output]
  rw [measuredBase,List.length_replicate,finalStore] at clearing
  have combined := measurement.sequence (emission.sequence clearing)
  refine ⟨scale*(5*(store (w 0)).length+3)+1+(emitTime+1+(scale*(store (w 0)).length+1)),?_,combined⟩
  simp [PolynomialWorkspace.powerRoles,measured] at emitBound
  have inner : scale*(store (w 0)).length+1≤(scale+1)*((store (w 0)).length+1) := by nlinarith
  have powered := Nat.pow_le_pow_left inner 2
  rw [Nat.mul_pow] at powered
  have lengthBound : (store (w 0)).length+1≤((store (w 0)).length+1)^2 := by nlinarith
  have scaled := Nat.mul_le_mul_left (6*scale+6) lengthBound
  unfold emitScaledNaturalCoefficient
  nlinarith

end Counting.StackMachine.Routine
