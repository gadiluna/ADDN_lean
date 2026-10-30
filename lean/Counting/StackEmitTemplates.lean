import Counting.StackEmitClause
import Counting.StackScaleLength
import Counting.StackPolynomialLength

namespace Counting.StackMachine.Routine

abbrev clauseCodec := Encoding.list literalCodec

def shiftedClauses (base : Nat) (clauses : List (List (Nat × Bool))) : List (List (Nat × Bool)) :=
  clauses.map (shiftedLiterals base)

def emitClauses (extra : Nat) (w : PowerWorkspace extra) : List (List (Nat × Bool)) → Routine (extra+3)
  | [] => skip (extra+3)
  | clause::rest => sequence (emitClauses extra w rest) (emitClause extra w clause)

def clausesCoefficient : List (List (Nat × Bool)) → Nat
  | [] => 0
  | clause::rest => clausesCoefficient rest+1+clauseCoefficient clause

theorem emitClauses_executes (extra : Nat) (w : PowerWorkspace extra) (clauses : List (List (Nat × Bool)))
    (store : Fin (extra+5) → List Bool) (counterEmpty : store (w 2) = [])
    (binaryEmpty : store (w 3) = []) (workEmpty : store (w 4) = []) :
    ∃ transitions ≤ clausesCoefficient clauses*((store (w 0)).length+1)^2,
      Executes (emitClauses extra w clauses) store transitions
        (Function.update store (w 1)
          (Encoding.sequence clauseCodec (shiftedClauses (store (w 0)).length clauses)++store (w 1))) := by
  induction clauses generalizing store with
  | nil =>
      refine ⟨0,by simp [clausesCoefficient],?_⟩
      simpa only [emitClauses,shiftedClauses,List.map_nil,Encoding.sequence,List.nil_append,Function.update_eq_self] using skip_executes store
  | cons clause rest ih =>
      obtain ⟨tailTime,tailBound,tailRun⟩ := ih store counterEmpty binaryEmpty workEmpty
      let middle := Function.update store (w 1)
        (Encoding.sequence clauseCodec (shiftedClauses (store (w 0)).length rest)++store (w 1))
      obtain ⟨headTime,headBound,headRun⟩ := emitClause_executes extra w clause middle
        (by simp [middle,w.injective.eq_iff,counterEmpty])
        (by simp [middle,w.injective.eq_iff,binaryEmpty])
        (by simp [middle,w.injective.eq_iff,workEmpty])
      have combined := tailRun.sequence headRun
      refine ⟨tailTime+1+headTime,?_,?_⟩
      · simp only [middle,Function.update_of_ne (workspace_ne w (by decide : (0 : Fin 5) ≠ 1))] at headBound
        have positive : 1 ≤ ((store (w 0)).length+1)^2 := Nat.one_le_pow 2 _ (by omega)
        unfold clausesCoefficient
        nlinarith
      · simpa only [emitClauses,middle,Function.update_self,Function.update_idem,
          Function.update_of_ne (workspace_ne w (by decide : (0 : Fin 5) ≠ 1)),shiftedClauses,
          List.map_cons,Encoding.sequence,List.append_assoc] using combined

/-- Roles are counter, scaled base, output, and three empty scratch stacks. -/
def scaledClauses (extra : Nat) (w : PolynomialWorkspace extra) (scale : Nat)
    (clauses : List (List (Nat × Bool))) : Routine (extra+4) :=
  sequence (scaleLength (extra+3) (w 0) (w 1) (w 5) scale)
    (sequence (emitClauses (extra+1) w.powerRoles clauses) (clear (w 1)))

def scaledClausesCoefficient (scale : Nat) (clauses : List (List (Nat × Bool))) : Nat :=
  clausesCoefficient clauses*(scale+1)^2+6*scale+3

theorem scaledClauses_executes (extra : Nat) (w : PolynomialWorkspace extra) (scale : Nat)
    (clauses : List (List (Nat × Bool))) (store : Fin (extra+6) → List Bool)
    (baseEmpty : store (w 1)=[]) (counterEmpty : store (w 3)=[])
    (binaryEmpty : store (w 4)=[]) (workEmpty : store (w 5)=[]) :
    ∃ transitions ≤ scaledClausesCoefficient scale clauses*((store (w 0)).length+1)^2,
      Executes (scaledClauses extra w scale clauses) store transitions
        (Function.update store (w 2)
          (Encoding.sequence clauseCodec (shiftedClauses (scale*(store (w 0)).length) clauses)++store (w 2))) := by
  have distinct {a b : Fin 6} (different : a ≠ b) : w a ≠ w b := fun same => different (w.injective same)
  let measured := Function.update store (w 1) (List.replicate (scale*(store (w 0)).length) true)
  have measurement : Executes (scaleLength (extra+3) (w 0) (w 1) (w 5) scale) store
      (scale*(5*(store (w 0)).length+3)) measured := by
    simpa only [baseEmpty,List.append_nil,measured] using
      scaleLength_executes (extra+3) (w 0) (w 1) (w 5)
        (distinct (by decide)) (distinct (by decide)) (distinct (by decide)) scale store workEmpty
  obtain ⟨emitTime,emitBound,emitted⟩ := emitClauses_executes (extra+1) w.powerRoles clauses measured
    (by simp [measured,PolynomialWorkspace.powerRoles,w.injective.eq_iff,counterEmpty])
    (by simp [measured,PolynomialWorkspace.powerRoles,w.injective.eq_iff,binaryEmpty])
    (by simp [measured,PolynomialWorkspace.powerRoles,w.injective.eq_iff,workEmpty])
  let afterEmit := Function.update measured (w 2)
    (Encoding.sequence clauseCodec (shiftedClauses (scale*(store (w 0)).length) clauses)++store (w 2))
  have emission : Executes (emitClauses (extra+1) w.powerRoles clauses) measured emitTime afterEmit := by
    simpa [PolynomialWorkspace.powerRoles,measured,afterEmit,w.injective.eq_iff] using emitted
  have clearing := clear_executes (w 1) afterEmit
  have combined := measurement.sequence (emission.sequence clearing)
  have measuredBase : afterEmit (w 1) = List.replicate (scale*(store (w 0)).length) true := by
    simp [afterEmit,measured,w.injective.eq_iff]
  refine ⟨scale*(5*(store (w 0)).length+3)+1+(emitTime+1+((afterEmit (w 1)).length+1)),?_,?_⟩
  · simp [PolynomialWorkspace.powerRoles,measured] at emitBound
    rw [measuredBase,List.length_replicate]
    have baseBound : scale*(store (w 0)).length+1 ≤ (scale+1)*((store (w 0)).length+1) := by nlinarith
    have scaled := Nat.mul_le_mul_left (clausesCoefficient clauses) (Nat.pow_le_pow_left baseBound 2)
    have one : 1 ≤ ((store (w 0)).length+1)^2 := Nat.one_le_pow 2 _ (by omega)
    have lengthBound : (store (w 0)).length+1 ≤ ((store (w 0)).length+1)^2 := by
      nlinarith
    have linear := Nat.mul_le_mul_left (6*scale+3) lengthBound
    unfold scaledClausesCoefficient
    nlinarith
  · have finalStore : Function.update afterEmit (w 1) [] = Function.update store (w 2)
        (Encoding.sequence clauseCodec (shiftedClauses (scale*(store (w 0)).length) clauses)++store (w 2)) := by
      funext register
      by_cases base : register = w 1
      · subst register; simp [baseEmpty,w.injective.eq_iff]
      · by_cases output : register = w 2
        · subst register; simp [afterEmit,w.injective.eq_iff]
        · simp [afterEmit,measured,base,output]
    rw [finalStore] at combined
    exact combined

end Counting.StackMachine.Routine
