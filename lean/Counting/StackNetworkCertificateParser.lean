import Counting.NetworkCertificateSpec
import Counting.NetworkRecognitionParser
import Counting.StackRealizabilityVistaParser

namespace Counting.StackMachine.NetworkCertificate
open EncodingPrograms
set_option backward.isDefEq.respectTransparency false

theorem vista_encoding_positive (vista : Executable.Vista) :
    0 < (Encoding.vista.encode vista).length := by
  change 0 < ((Encoding.list Encoding.node).encode vista.nodes.toList ++
    Encoding.natural.encode vista.bottom).length
  simp only [List.length_append,Encoding.natural_length]
  omega

theorem witness_encoding_positive (certificate : Encoding.TwoOrderData) :
    0 < (Encoding.twoOrderWitness.encode certificate).length := by
  simp only [Encoding.twoOrderWitness,Encoding.orderWitness,Encoding.product,
    List.length_append,Encoding.natural_length]
  omega

def viewsParser : VerifiedParser 15 0 1 2 (List Executable.Vista) (Encoding.list Encoding.vista) :=
  listParser 0 NetworkRecognition.roundRoles DagParser.vista (by decide) vista_encoding_positive

def certificatesParser : VerifiedParser 15 0 1 2 (List Encoding.TwoOrderData) Encoding.networkWitness :=
  listParser 0 DagParser.outerRoles VistaComplement.witnessParser (by decide) witness_encoding_positive

def parser : VerifiedParser 15 0 1 2 Counting.NetworkCertificate.Input Counting.NetworkCertificate.codec :=
  DagParser.natural.product (by decide) (by decide) (by decide)
    (viewsParser.product (by decide) (by decide) (by decide) certificatesParser)

theorem parser_computes : ComputesIn parser.recognition.program
    (fun input => [(Counting.NetworkCertificate.codec.decodeExact input).isSome])
    (Complexity.polynomial (parser.coefficient+20) (max 1 parser.exponent)) :=
  parser.recognition_computes

theorem parser_exponent : max 1 parser.exponent ≤ 27 := by decide
theorem viewsParser_coefficient : viewsParser.coefficient ≤ 20000 := by decide
theorem viewsParser_exponent : viewsParser.exponent ≤ 5 := by decide
theorem certificatesParser_coefficient : certificatesParser.coefficient ≤ 20000 := by decide
theorem certificatesParser_exponent : certificatesParser.exponent ≤ 5 := by decide

end Counting.StackMachine.NetworkCertificate
