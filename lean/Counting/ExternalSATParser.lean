import Counting.ExternalSATVerification
import Counting.StackEncodingDagParser
import Counting.StackEncodingParserRecognition

namespace Counting.External.SATVerification
open StackMachine.EncodingPrograms

/-- The exact raw CNF grammar has an executable parser with bounded headers.
Marker values and variable bounds are checked by the separate evaluator. -/
def literalParser : VerifiedParser 15 0 1 2 (Nat×Bool) (Encoding.product Encoding.natural Encoding.boolean) :=
  DagParser.natural.product (by decide) (by decide) (by decide) DagParser.boolean

def clauseParser : VerifiedParser 15 0 1 2 (List (Nat×Bool))
    (Encoding.list (Encoding.product Encoding.natural Encoding.boolean)) :=
  listParser 0 DagParser.innerRoles literalParser (by decide) (by
    intro literal
    simp only [Encoding.product,List.length_append,Encoding.natural_length,Encoding.boolean]
    simp)

def formulaParser : VerifiedParser 15 0 1 2 (List (List (Nat×Bool)))
    (Encoding.list (Encoding.list (Encoding.product Encoding.natural Encoding.boolean))) :=
  listParser 0 DagParser.outerRoles clauseParser (by decide) (by
    intro clause
    rw [Encoding.list_length]
    omega)

def tableParser : VerifiedParser 15 0 1 2 (List Bool) (Encoding.list Encoding.boolean) :=
  listParser 0 DagParser.innerRoles DagParser.boolean (by decide) (by intro bit;simp [Encoding.boolean])

def rawParser : VerifiedParser 15 0 1 2 CNFEncoding.Raw CNFEncoding.rawCodec :=
  tableParser.product (by decide) (by decide) (by decide) formulaParser

theorem rawParser_computesCleanIn :
    Complexity.ComputesCleanIn (StackMachine.Compiler.compile rawParser.recognition.program)
      (fun input => [(CNFEncoding.rawCodec.decodeExact input).isSome])
      (Complexity.polynomial (20*(rawParser.coefficient+40)^2) (2*(max 1 rawParser.exponent+1))) :=
  rawParser.recognition_computesCleanIn

end Counting.External.SATVerification
