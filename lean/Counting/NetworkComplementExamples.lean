import Counting.NetworkCertificatePrefix
import Counting.StackNetworkComplementEntry

namespace Counting.NetworkComplement.Examples

/-- Invalid network words are negative language instances, so their
complementary verifier accepts even a malformed certificate suffix. -/
theorem malformed_network_accepts_complement (witness : List Bool) :
    NetworkCertificate.binaryRawNetworkComplementVerifier [] witness=true := by
  simp only [NetworkCertificate.binaryRawNetworkComplementVerifier,
    show Encoding.decodeNetwork? []=none by decide]

/-- A missing certificate-list header is rejected after two valid prefixes. -/
theorem missing_certificate_header (ell : Nat) (views : Array Executable.Vista) :
    NetworkCertificate.predicate (NetworkCertificate.inputWord ell views [])=false := by
  rw [NetworkCertificate.predicate_inputWord]
  rfl

/-- The canonical empty certificate list is accepted precisely when the
reconstructed view list is also empty at this component boundary. -/
theorem empty_arrays (ell : Nat) :
    NetworkCertificate.predicate (NetworkCertificate.inputWord ell #[] [false])=true := by
  rw [NetworkCertificate.predicate_inputWord]
  rfl

theorem missing_agent_certificate (ell : Nat) (view : Executable.Vista) :
    NetworkCertificate.predicate (NetworkCertificate.inputWord ell #[view] [false])=false := by
  rw [NetworkCertificate.predicate_inputWord]
  rfl

end Counting.NetworkComplement.Examples
