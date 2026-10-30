import Counting.NetworkCertificateSpec

namespace Counting.NetworkCertificate

theorem empty_input_accepts (ell : Nat) : predicate (codec.encode (ell,[],[]))=true := by
  rw [predicate_encoded,check_empty]

theorem missing_certificate_rejected (ell : Nat) (vista : Executable.Vista) :
    predicate (codec.encode (ell,[vista],[]))=false := by
  rw [predicate_encoded]
  exact check_length_mismatch ell [vista] [] (by simp)

theorem extra_certificate_rejected (ell : Nat) (certificate : Encoding.TwoOrderData) :
    predicate (codec.encode (ell,[],[certificate]))=false := by
  rw [predicate_encoded]
  exact check_length_mismatch ell [] [certificate] (by simp)

theorem empty_word_rejected : predicate []=false := by decide

end Counting.NetworkCertificate
