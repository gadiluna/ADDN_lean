import Counting.ExternalFiniteConstraints
import Counting.StackMultiTemplates

namespace Counting.External.CookLevin.StackGenerator
open StackMachine StackMachine.Routine FiniteConstraints

/-- Arity-four local relation with an explicit position map. The allowed
relation is fixed by the verifier transition table, not runtime input data. -/
def localConstraint {nodes alphabet : Nat} (position : Fin 4 → Fin nodes)
    (allowed : (Fin 4 → Fin alphabet) → Bool) : Constraint nodes alphabet :=
  ⟨4,position,allowed⟩

def localTemplate (alphabet : Nat) (allowed : (Fin 4 → Fin alphabet) → Bool) : List (List LiteralTemplate) :=
  ((tuples alphabet 4).filter (fun tuple => !allowed tuple)).map
    (fun tuple => (List.finRange 4).map (fun index => ⟨index,(tuple index).val,false⟩))

theorem localConstraint_raw (extra : Nat) (w : ClauseWorkspace extra) {nodes alphabet : Nat}
    (position : Fin 4 → Fin nodes) (allowed : (Fin 4 → Fin alphabet) → Bool)
    (store : Fin (extra+8) → List Bool)
    (bases : ∀ index : Fin 4, (store (w (index.castAdd 4))).length=alphabet*(position index).val) :
    (localTemplate alphabet allowed).map (List.map (LiteralTemplate.value w store)) =
      (localConstraint position allowed).toCNF.map (List.map CNFEncoding.literalRaw) := by
  unfold localTemplate localConstraint Constraint.toCNF
  simp only [List.map_map,Function.comp_def]
  apply congrArg (List.map · ((tuples alphabet 4).filter (fun tuple => !allowed tuple)))
  funext tuple
  apply congrArg (List.map · (List.finRange 4))
  funext index
  simp [LiteralTemplate.value,bases index,CNFEncoding.literalRaw,lit,bitIndex,finProdFinEquiv,Nat.add_comm]

def localConstraintRoutine (extra : Nat) (w : ClauseWorkspace extra) (alphabet : Nat)
    (allowed : (Fin 4 → Fin alphabet) → Bool) : Routine (extra+6) :=
  emitMultiClauses extra w (localTemplate alphabet allowed)

/-- Exact executable emission of all forbidden-tuple clauses for a local
transition. Four bases are supplied as unary identifiers and preserved. -/
theorem localConstraintRoutine_executes (extra : Nat) (w : ClauseWorkspace extra) {nodes alphabet : Nat}
    (position : Fin 4 → Fin nodes) (allowed : (Fin 4 → Fin alphabet) → Bool)
    (store : Fin (extra+8) → List Bool)
    (bases : ∀ index : Fin 4, (store (w (index.castAdd 4))).length=alphabet*(position index).val)
    (counterEmpty : store (w 5)=[]) (binaryEmpty : store (w 6)=[]) (workEmpty : store (w 7)=[]) :
    ∃ transitions ≤ multiClausesCoefficient (localTemplate alphabet allowed)*(alphabet*nodes+1)^2,
      Executes (localConstraintRoutine extra w alphabet allowed) store transitions
        (Function.update store (w 4)
          (Encoding.sequence clauseCodec
            ((localConstraint position allowed).toCNF.map (List.map CNFEncoding.literalRaw))++store (w 4))) := by
  have bounded : ∀ index : Fin 4, (store (w (index.castAdd 4))).length ≤ alphabet*nodes := by
    intro index
    rw [bases]
    exact Nat.mul_le_mul_left alphabet (Nat.le_of_lt (position index).isLt)
  obtain ⟨time,bound,executed⟩ := emitMultiClauses_executes extra w (localTemplate alphabet allowed) store
    (alphabet*nodes) bounded counterEmpty binaryEmpty workEmpty
  rw [localConstraint_raw extra w position allowed store bases] at executed
  exact ⟨time,bound,executed⟩

end Counting.External.CookLevin.StackGenerator
