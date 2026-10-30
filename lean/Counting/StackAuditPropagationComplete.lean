import Counting.StackAuditPropagationFinish
import Counting.StackAuditPropagationRounds

namespace Counting.StackMachine.AuditPropagation
open Routine
set_option backward.isDefEq.respectTransparency false

abbrev completePropagation : Routine 42 := sequence preparePropagationInput
  (sequence preparePropagationRounds (sequence propagatePrepared finishPropagation))

def propagationBudget (anchor : Nat) (vista : Executable.Vista) (values : Array Nat) : Nat :=
  5000*((propagationInputWord anchor vista values).length+1)^3+
    1000*(vista.nodes.size+anchor.size+1)^3+preparedBudget anchor vista values+
    10*((Encoding.vista.encode vista).length+
      (Encoding.sequence Encoding.node vista.nodes.toList++Encoding.natural.encode vista.bottom).length+
      2*vista.nodes.size+anchor.size+(propagationOutputWord anchor vista values).length+4)+3

/-- The complete serialized computation of `propagateWeights`. It reads the
node and value counts, constructs the zero array, assigns the anchor zip,
performs every backward pass, and erases all auxiliary registers. No validity,
positivity, or equality between the number of values and anchor nodes is assumed. -/
theorem completePropagation_executes (anchor : Nat) (vista : Executable.Vista) (values : Array Nat)
    (fits : anchor ≤ vista.nodes.size) :
    ∃ time ≤ propagationBudget anchor vista values,
      Executes completePropagation (inputStore 42 (propagationInputWord anchor vista values)) time
        (outputStore 42 (propagationOutputWord anchor vista values)) := by
  obtain ⟨inputTime,inputBound,a⟩ := preparePropagationInput_executes anchor vista values
  obtain ⟨roundTime,roundBound,b⟩ := preparePropagationRounds_setup anchor vista values fits
  obtain ⟨bodyTime,bodyBound,c⟩ := propagatePrepared_executes anchor vista values fits
  obtain ⟨finishTime,finishBound,d⟩ := finishPropagation_executes anchor vista values
  have initialFile : propagationInputFile (propagationInputWord anchor vista values) [] [] [] []=
      inputStore 42 (propagationInputWord anchor vista values) := by
    funext i
    fin_cases i <;> simp [propagationInputFile,inputStore]
  rw [initialFile] at a
  refine ⟨_,?_,a.sequence (b.sequence (c.sequence d))⟩
  dsimp only [propagationBudget]
  omega

end Counting.StackMachine.AuditPropagation
