import Counting.StackEncodingDagParser
import Counting.StackEncodingParserRecognition
import Counting.EncodingRecognition

namespace Counting.StackMachine.VistaComplement
open EncodingPrograms

/-- Canonical syntax recognition is separate from semantic realizability.
The two parsers are built from the existing charged codec combinators. -/
def inputParser : VerifiedParser 15 0 1 2 (Executable.Vista×Nat) Encoding.vistaInput :=
  DagParser.vista.product (by decide) (by decide) (by decide) DagParser.natural

def orderParser : VerifiedParser 15 0 1 2 (Nat×List Nat) Encoding.orderWitness :=
  DagParser.natural.product (by decide) (by decide) (by decide) DagParser.naturals

def witnessParser : VerifiedParser 15 0 1 2 ((Nat×List Nat)×(Nat×List Nat)) Encoding.twoOrderWitness :=
  orderParser.product (by decide) (by decide) (by decide) orderParser

theorem inputParser_computes : ComputesIn inputParser.recognition.program
    (fun input=>[(Encoding.vistaInput.decodeExact input).isSome])
    (Complexity.polynomial (inputParser.coefficient+20) (max 1 inputParser.exponent)) := by
  exact inputParser.recognition_computes

theorem witnessParser_computes : ComputesIn witnessParser.recognition.program
    (fun input=>[(Encoding.twoOrderWitness.decodeExact input).isSome])
    (Complexity.polynomial (witnessParser.coefficient+20) (max 1 witnessParser.exponent)) :=
  witnessParser.recognition_computes

theorem inputParser_exponent : max 1 inputParser.exponent ≤ 25 := by decide
theorem witnessParser_exponent : max 1 witnessParser.exponent ≤ 25 := by decide

end Counting.StackMachine.VistaComplement
