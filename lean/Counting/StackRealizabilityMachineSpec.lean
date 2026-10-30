import Counting.StackRealizabilityMachine
import Counting.RealizabilityVerifierComplete

namespace Counting.StackMachine.RealizabilityCheck

/-- Canonically encoded accepted certificates describe actual realizations. -/
theorem encodedVerifier_sound (vista : Executable.Vista) (values : List Nat) (ell order : Nat)
    (accepted : encodedVerifier (Encoding.verifierInput.encode (vista,values,ell,order))=true) :
    vista.valid=true ∧ Realizability.Realizable ell order vista.denotes := by
  rw [encodedVerifier_encode] at accepted
  exact ⟨((RealizabilityVerifier.verify_iff_certificate vista values.toArray ell order).mp accepted).1,
    RealizabilityVerifier.verify_sound vista values.toArray ell order accepted⟩

/-- Existential completeness concerns the compact count array, not an
expanded realization. The machine above operates on these exact bits. -/
theorem exists_encodedVerifier_iff (vista : Executable.Vista) (ell order : Nat) :
    (∃ values : List Nat, encodedVerifier (Encoding.verifierInput.encode (vista,values,ell,order))=true) ↔
      vista.valid=true ∧ Realizability.Realizable ell order vista.denotes := by
  constructor
  · rintro ⟨values,accepted⟩
    exact encodedVerifier_sound vista values ell order accepted
  · intro possible
    obtain ⟨weights,accepted⟩ := (RealizabilityVerifier.exists_verified_iff vista ell order).mpr possible
    refine ⟨weights.toList,?_⟩
    rw [encodedVerifier_encode,Array.toArray_toList]
    exact accepted

end Counting.StackMachine.RealizabilityCheck
