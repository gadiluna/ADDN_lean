import Counting.ExternalOneHotLayout

namespace Counting.External.CookLevin.StackGenerator
open StackMachine StackMachine.Routine FiniteConstraints

/-- Emit the one-hot clauses for a runtime number of cells. The alphabet
and its local templates are fixed in the generated finite control. -/
def oneHotRoutine (extra : Nat) (w : PolynomialWorkspace extra) (alphabet : Nat) : Routine (extra+4) :=
  forEach (w 0) (scaledClauses extra w alphabet (oneHotTemplate alphabet))

def oneHotBodyCoefficient (alphabet : Nat) : Nat := scaledClausesCoefficient alphabet (oneHotTemplate alphabet)

theorem oneHotRoutine_executes (extra : Nat) (w : PolynomialWorkspace extra) (alphabet : Nat)
    (store : Fin (extra+6) → List Bool) (baseEmpty : store (w 1)=[])
    (counterEmpty : store (w 3)=[]) (binaryEmpty : store (w 4)=[]) (workEmpty : store (w 5)=[]) :
    ∃ transitions ≤ (store (w 0)).length*(oneHotBodyCoefficient alphabet*((store (w 0)).length+1)^2+2)+1,
      Executes (oneHotRoutine extra w alphabet) store transitions
        (Function.update (Function.update store (w 0) []) (w 2)
          (Encoding.sequence clauseCodec
            ((oneHot (store (w 0)).length alphabet).map (List.map CNFEncoding.literalRaw))++store (w 2))) := by
  let invariant := fun state : Fin (extra+6) → List Bool =>
    (state (w 0)).length ≤ (store (w 0)).length ∧ state (w 1)=[] ∧
      state (w 3)=[] ∧ state (w 4)=[] ∧ state (w 5)=[]
  let chunk := fun cell => Encoding.sequence clauseCodec (shiftedClauses (alphabet*cell) (oneHotTemplate alphabet))
  have distinct {a b : Fin 6} (different : a ≠ b) : w a ≠ w b := fun same => different (w.injective same)
  have executes : ∀ state, invariant state → ∃ time ≤ oneHotBodyCoefficient alphabet*((store (w 0)).length+1)^2,
      Executes (scaledClauses extra w alphabet (oneHotTemplate alphabet)) state time (emitBody (w 0) (w 2) chunk state) := by
    intro state valid
    obtain ⟨time,bounded,run⟩ := scaledClauses_executes extra w alphabet (oneHotTemplate alphabet) state
      valid.2.1 valid.2.2.1 valid.2.2.2.1 valid.2.2.2.2
    refine ⟨time,bounded.trans ?_,run⟩
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right valid.1 1) 2)
  have consumeInvariant : ∀ state, invariant state → invariant (consume (w 0) state) := by
    intro state valid
    refine ⟨?_,?_,?_,?_,?_⟩
    · simp only [consume,Function.update_self,List.length_tail]
      exact (Nat.sub_le _ _).trans valid.1
    · simpa only [consume,Function.update_of_ne (distinct (by decide : (1 : Fin 6) ≠ 0))] using valid.2.1
    · simpa only [consume,Function.update_of_ne (distinct (by decide : (3 : Fin 6) ≠ 0))] using valid.2.2.1
    · simpa only [consume,Function.update_of_ne (distinct (by decide : (4 : Fin 6) ≠ 0))] using valid.2.2.2.1
    · simpa only [consume,Function.update_of_ne (distinct (by decide : (5 : Fin 6) ≠ 0))] using valid.2.2.2.2
  have emitInvariant : ∀ state, invariant state → invariant (emitBody (w 0) (w 2) chunk state) := by
    intro state valid
    simpa [invariant,emitBody,w.injective.eq_iff] using valid
  have valid : invariant store := ⟨le_rfl,baseEmpty,counterEmpty,binaryEmpty,workEmpty⟩
  obtain ⟨time,bounded,executed⟩ := descendingEmit_executes (w 0) (w 2) (distinct (by decide))
    (scaledClauses extra w alphabet (oneHotTemplate alphabet)) chunk invariant
    (oneHotBodyCoefficient alphabet*((store (w 0)).length+1)^2)
    executes consumeInvariant emitInvariant store valid
  refine ⟨time,bounded,?_⟩
  simpa only [oneHotRoutine,chunk,oneHot_encoded_chunks] using executed

/-- Cubic stack-time bound for all cells, including the last empty pop. -/
theorem oneHot_time_bound (cells alphabet : Nat) :
    cells*(oneHotBodyCoefficient alphabet*(cells+1)^2+2)+1 ≤
      (oneHotBodyCoefficient alphabet+3)*(cells+1)^3 := by
  have positive : 1 ≤ (cells+1)^3 := Nat.one_le_pow 3 _ (by omega)
  nlinarith [Nat.zero_le (oneHotBodyCoefficient alphabet)]

end Counting.External.CookLevin.StackGenerator
