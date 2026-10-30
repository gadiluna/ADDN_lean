import Counting.ExternalFormulaUnaryCount
import Counting.ExternalFormulaSerialization
import Counting.ExternalInitialBinaryTemplate
import Counting.ExternalTransitionEmission

namespace Counting.External.CookLevin.StackGenerator
open FiniteConstraints Tableau InitialRows StackMachine.Routine

theorem oneHot_length_template (cells alphabet : Nat) :
    (oneHot cells alphabet).length = cells*(oneHotTemplate alphabet).length := by
  have counted := congrArg List.length (oneHot_raw cells alphabet)
  simpa [List.length_flatMap,shiftedClauses,Nat.mul_comm] using counted

theorem initialBinary_length_template {time width : Nat} (setup : Setup width) (program : Machine.Program)
    (place : Fin (setup.capacity-1)) :
    (initialConstraint (T := time) (setup.binary program
      (adjacentLeft setup.capacity place) (adjacentRight setup.capacity place))).toCNF.length =
      (initialBinaryTemplate program).length := by
  simp only [Constraint.toCNF,initialConstraint,Setup.binary,initialBinaryTemplate,
    initialBinaryAllowed,List.length_map]

def transitionClauseCount (program : Machine.Program) : Nat :=
  (localTemplate (Cellular.alphabet program)
    (transitionAllowed (Cellular.dynamics program (finRotate 0)).rule)).length

theorem transition_length_template {time width : Nat} (program : Machine.Program)
    (round : Fin time) (place : Fin width) :
    (transitionConstraint (Cellular.dynamics program (finRotate width)) round place).toCNF.length =
      transitionClauseCount program := by
  simp only [transitionClauseCount,localTemplate,Constraint.toCNF,transitionConstraint,
    transitionAllowed,List.length_map]
  rfl

/-- Every coefficient depends only on the fixed verifier. Runtime operands
are unary dimensions already provided by generator preparation. -/
def formulaClauseCount (program : Machine.Program) (cells width capacity : Nat) : Nat :=
  cells*(oneHotTemplate (Cellular.alphabet program)).length+
  capacity*(Cellular.alphabet program-3)+(width-capacity)*(Cellular.alphabet program-1)+
  (capacity-1)*(initialBinaryTemplate program).length+
  (cells-width)*transitionClauseCount program+1

theorem formula_length_exact {time width : Nat} (setup : Setup width) (program : Machine.Program) :
    (Tableau.formula (T := time) (Cellular.dynamics program (finRotate width))
      (setup.constraints program) (Cellular.accept program)).length =
      formulaClauseCount program ((time+1)*width) width setup.capacity := by
  rw [Tableau.formula,FiniteConstraints.toCNF,Tableau.constraints,setup.constraints_adjacent]
  simp only [List.map_append,List.flatMap_append,List.flatMap_map,List.flatMap_assoc,
    List.length_append,List.length_singleton]
  rw [oneHot_length_template,initialUnary_block_length]
  simp only [List.length_flatMap,initialBinary_length_template,transition_length_template,
    List.map_const',List.length_finRange,List.sum_replicate]
  unfold formulaClauseCount
  have rows : (time+1)*width-width=time*width := by simp [Nat.add_mul]
  rw [rows]
  ring

end Counting.External.CookLevin.StackGenerator
