import Counting.StackEncodingDagParser
import Counting.StackEncodingParserRecognition

namespace Counting.StackMachine.EncodingPrograms.DagParser

def vistaRecognitionProgram : Program := vista.recognition.program

def nodeRecognitionProgram : Program := node.recognition.program

/-- Serialization recognition for arbitrary words, using the actual DAG
codec. Structural/semantic DAG validity is checked by a different procedure. -/
theorem vista_serialization_computes : ComputesIn vistaRecognitionProgram
    (fun input => [(Encoding.vista.decodeExact input).isSome])
    (Complexity.polynomial 3910 4) := by
  exact vista.recognition_computes

/-- The bound is on actual finite Turing-machine transitions, with the
entire tape clean on every accepted or rejected input. -/
theorem vista_serialization_computesCleanIn : Complexity.ComputesCleanIn
    (Compiler.compile vistaRecognitionProgram)
    (fun input => [(Encoding.vista.decodeExact input).isSome])
    (Complexity.polynomial 308898000 10) := by
  exact vista.recognition_computesCleanIn

theorem node_serialization_computesCleanIn : Complexity.ComputesCleanIn
    (Compiler.compile nodeRecognitionProgram)
    (fun input => [(Encoding.node.decodeExact input).isSome])
    (Complexity.polynomial 85615220 8) := by
  exact node.recognition_computesCleanIn

def verifierInputRecognitionProgram : Program := verifierInput.recognition.program

/-- Syntax alone for the complete realization-verifier input tuple. The
mathematical acceptance conditions of that verifier are separate. -/
theorem verifier_input_serialization_computesCleanIn : Complexity.ComputesCleanIn
    (Compiler.compile verifierInputRecognitionProgram)
    (fun input => [(Encoding.verifierInput.decodeExact input).isSome])
    (Complexity.polynomial 689842580 10) := by
  exact verifierInput.recognition_computesCleanIn

end Counting.StackMachine.EncodingPrograms.DagParser
