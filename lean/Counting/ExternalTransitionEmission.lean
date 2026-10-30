import Counting.ExternalConstraintGenerator
import Counting.ExternalTableau

namespace Counting.External.CookLevin.StackGenerator
open StackMachine StackMachine.Routine FiniteConstraints Tableau

def transitionAllowed {alphabet : Nat} (rule : (Fin 3 → Fin alphabet) → Fin alphabet)
    (tuple : Fin 4 → Fin alphabet) : Bool := decide (tuple 3=rule ![tuple 0,tuple 1,tuple 2])

/-- The transition emitter contains only the fixed finite local rule. Row
width and time are supplied through four runtime base registers. -/
def transitionRoutine (extra : Nat) (w : ClauseWorkspace extra) (alphabet : Nat)
    (rule : (Fin 3 → Fin alphabet) → Fin alphabet) : Routine (extra+6) :=
  localConstraintRoutine extra w alphabet (transitionAllowed rule)

theorem transitionRoutine_executes (extra : Nat) (w : ClauseWorkspace extra) {time width alphabet : Nat}
    (dynamics : Dynamics width alphabet) (round : Fin time) (place : Fin width)
    (store : Fin (extra+8) → List Bool)
    (bases : ∀ position : Fin 4, (store (w (position.castAdd 4))).length =
      alphabet*((transitionConstraint dynamics round place).position position).val)
    (counterEmpty : store (w 5)=[]) (binaryEmpty : store (w 6)=[]) (workEmpty : store (w 7)=[]) :
    ∃ transitions ≤ multiClausesCoefficient (localTemplate alphabet (transitionAllowed dynamics.rule))*
        (alphabet*((time+1)*width)+1)^2,
      Executes (transitionRoutine extra w alphabet dynamics.rule) store transitions
        (Function.update store (w 4)
          (Encoding.sequence clauseCodec
            ((transitionConstraint dynamics round place).toCNF.map (List.map CNFEncoding.literalRaw))++store (w 4))) := by
  exact localConstraintRoutine_executes extra w (transitionConstraint dynamics round place).position
    (transitionAllowed dynamics.rule) store bases counterEmpty binaryEmpty workEmpty

end Counting.External.CookLevin.StackGenerator
