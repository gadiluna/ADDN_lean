import Counting.ExternalInitialRows
import Counting.StackEmitTemplates

namespace Counting.External.CookLevin.StackGenerator
open StackMachine StackMachine.Routine FiniteConstraints

def unaryConstraint {nodes alphabet : Nat} (position : Fin nodes) (allowed : Fin alphabet → Bool) : Constraint nodes alphabet :=
  ⟨1,fun _ => position,fun tuple => allowed (tuple 0)⟩

def unaryTemplate (alphabet : Nat) (allowed : Fin alphabet → Bool) : List (List (Nat × Bool)) :=
  ((tuples alphabet 1).filter (fun tuple => !allowed (tuple 0))).map
    (fun tuple => (List.finRange 1).map (fun index => ((tuple index).val,false)))

theorem unaryConstraint_raw {nodes alphabet : Nat} (position : Fin nodes) (allowed : Fin alphabet → Bool) :
    shiftedClauses (alphabet*position.val) (unaryTemplate alphabet allowed)=
      (unaryConstraint position allowed).toCNF.map (List.map CNFEncoding.literalRaw) := by
  unfold unaryTemplate unaryConstraint Constraint.toCNF shiftedClauses
  simp only [List.map_map,Function.comp_def]
  apply congrArg (List.map · ((tuples alphabet 1).filter (fun tuple => !allowed (tuple 0))))
  funext tuple
  simp [shiftedLiterals,List.map_map,CNFEncoding.literalRaw,lit,bitIndex,finProdFinEquiv,Nat.add_comm,Function.comp_def]

def unaryRoutine (extra : Nat) (w : PolynomialWorkspace extra) (alphabet : Nat)
    (allowed : Fin alphabet → Bool) : Routine (extra+4) :=
  scaledClauses extra w alphabet (unaryTemplate alphabet allowed)

theorem unaryRoutine_executes (extra : Nat) (w : PolynomialWorkspace extra) {nodes alphabet : Nat}
    (position : Fin nodes) (allowed : Fin alphabet → Bool) (store : Fin (extra+6) → List Bool)
    (indexValue : (store (w 0)).length=position.val)
    (baseEmpty : store (w 1)=[]) (counterEmpty : store (w 3)=[])
    (binaryEmpty : store (w 4)=[]) (workEmpty : store (w 5)=[]) :
    ∃ transitions ≤ scaledClausesCoefficient alphabet (unaryTemplate alphabet allowed)*(position.val+1)^2,
      Executes (unaryRoutine extra w alphabet allowed) store transitions
        (Function.update store (w 2)
          (Encoding.sequence clauseCodec
            ((unaryConstraint position allowed).toCNF.map (List.map CNFEncoding.literalRaw))++store (w 2))) := by
  obtain ⟨transitions,bound,run⟩ := scaledClauses_executes extra w alphabet (unaryTemplate alphabet allowed) store
    baseEmpty counterEmpty binaryEmpty workEmpty
  rw [indexValue] at bound run
  rw [unaryConstraint_raw] at run
  exact ⟨transitions,bound,run⟩

inductive InitialSymbolKind where
  | blank | zero | one | witness
  deriving DecidableEq

def InitialSymbolKind.allowed : InitialSymbolKind → Machine.Symbol → Prop
  | .blank,symbol => symbol=.blank
  | .zero,symbol => symbol=.zero
  | .one,symbol => symbol=.one
  | .witness,symbol => WitnessWord.permitted symbol

instance (kind : InitialSymbolKind) (symbol : Machine.Symbol) : Decidable (kind.allowed symbol) := by
  cases kind <;> unfold InitialSymbolKind.allowed <;> infer_instance

def initialAllowed (program : Machine.Program) (head : Bool) (kind : InitialSymbolKind)
    (value : Fin (Cellular.alphabet program)) : Bool :=
  let cell := (Cellular.cellEquiv program).symm value
  decide (cell.2=(if head then some 0 else none) ∧ kind.allowed cell.1)

/-- Initial-row data selects among eight fixed finite relations; templates
do not depend on any hidden global computation or expanded tableau. -/
def initialUnaryRoutine (extra : Nat) (w : PolynomialWorkspace extra) (program : Machine.Program)
    (head : Bool) (kind : InitialSymbolKind) : Routine (extra+4) :=
  unaryRoutine extra w (Cellular.alphabet program) (initialAllowed program head kind)

end Counting.External.CookLevin.StackGenerator
