import Counting.StackDagValidator
import Counting.DagSemanticsSyntax
import Counting.MachineBooleanDecision

/-! The binary syntax language has a concrete polynomial-time decider.
Its semantics includes all parent, red-incidence, uniqueness and exact
backward-closure conditions of the canonical DAG representation. -/
namespace Counting.StackMachine.DagValidation

theorem validWord_true_iff_syntax (input : List Bool) : validWord input=true ↔
    ∃ vista,Encoding.vista.encode vista=input ∧ Executable.VistaSyntax vista:=by
  rw [validWord_true_iff]
  simp only [Executable.valid_iff_syntax]

def syntaxLanguage : Complexity.Language:=
  Complexity.encodedLanguage Encoding.vista Executable.VistaSyntax

def syntaxDecision : Machine.Program:=
  Machine.compose (Compiler.compile validationProgram) Machine.booleanDecision

def syntaxTimeCoefficient : Nat:=Complexity.compositionCoefficient (20*(225000040)^2) 1 0
def syntaxTimeExponent : Nat:=Complexity.compositionExponent 14 0

theorem syntaxDecision_decides : Complexity.DecidesIn syntaxDecision syntaxLanguage
    (Complexity.polynomial syntaxTimeCoefficient syntaxTimeExponent):=by
  have decision:=validation_computesCleanIn.boolean_decides
  refine ⟨decision.1,?_⟩
  intro input
  exact (decision.2 input).trans (validWord_true_iff_syntax input)

theorem syntaxLanguage_in_P : Complexity.P syntaxLanguage:=
  ⟨syntaxDecision,syntaxTimeCoefficient,syntaxTimeExponent,syntaxDecision_decides⟩

end Counting.StackMachine.DagValidation
