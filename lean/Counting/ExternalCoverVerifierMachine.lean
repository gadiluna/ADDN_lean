import Counting.ExternalCoverVerifierEntry
import Counting.ExternalCoverMachine
import Counting.MachineBooleanDecision

namespace Counting.External.CoverVerification
open StackMachine
set_option maxRecDepth 10000

/-- The physical input is role 63 and the single Boolean output is role 1. -/
def canonicalWorkspace : VerifierWorkspace 0 :=
  ⟨![63,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,0],by decide⟩

def stackVerifier : Program := (entryRoutine 0 canonicalWorkspace).program

/-- A total executable verifier, including every malformed input string. -/
theorem stackVerifier_computes : ComputesIn stackVerifier (fun input => [verify input])
    (Complexity.polynomial verifierCoefficient 5) := by
  intro input
  let initialStore := (initial stackVerifier input).store
  have empty : ∀ i : Fin 64,i≠63 → initialStore (canonicalWorkspace i)=[] := by
    intro i different
    have ne : canonicalWorkspace i≠0 := by
      intro same
      exact different (canonicalWorkspace.injective (same.trans (show 0=canonicalWorkspace 63 from rfl)))
    change (if canonicalWorkspace i=(0:Fin 64) then input else [])=[]
    exact if_neg ne
  obtain ⟨time,bound,result,execution,output⟩ := entryRoutine_executes 0 canonicalWorkspace initialStore empty
  have source : initialStore (canonicalWorkspace 63)=input := rfl
  rw [source] at bound output
  obtain ⟨finish,ran,halted,finalStore⟩ := execution
  refine ⟨time,finish,bound,⟨ran,halted⟩,?_⟩
  rw [finalStore]
  exact output

def transducer : Machine.Program := Compiler.compile stackVerifier

theorem transducer_computesCleanIn : Complexity.ComputesCleanIn transducer (fun input => [verify input])
    (Complexity.polynomial (20*(verifierCoefficient+67)^2) 12) :=
  Compiler.computesCleanIn_polynomial verifierCoefficient 5 stackVerifier_computes

/-- Acceptance reads the produced bit in a charged physical transition. -/
def verifier : Machine.Program := Machine.compose transducer Machine.booleanDecision

def timeCoefficient := Complexity.compositionCoefficient (20*(verifierCoefficient+67)^2) 1 0

def timeExponent := Complexity.compositionExponent 12 0

theorem verifier_decides : Complexity.DecidesIn verifier {input | verify input=true}
    (Complexity.polynomial timeCoefficient timeExponent) :=
  transducer_computesCleanIn.boolean_decides

end Counting.External.CoverVerification

namespace Counting.External.CoverMachine

/-- Membership in NP uses one witness bit per explicitly listed triple.
The verifier parses and checks every malformed input in polynomial time. -/
theorem X3C_NP : Complexity.NP X3CLanguage := by
  refine ⟨CoverVerification.verifier,CoverVerification.timeCoefficient,CoverVerification.timeExponent,1,1,
    CoverVerification.verifier_decides.1,?_⟩
  intro input
  constructor
  · intro member
    obtain ⟨bits,bound,accepted⟩ := (CoverVerification.binaryX3C_iff_bounded_mask input).mp member
    refine ⟨bits,?_,?_⟩
    · simpa only [Complexity.polynomial,pow_one,one_mul] using bound.trans (Nat.le_succ _)
    · apply (CoverVerification.verifier_decides.2 _).mpr
      change CoverVerification.verify (Encoding.pairWords input bits)=true
      rwa [CoverVerification.verify_pairWords]
  · rintro ⟨bits,_bound,accepted⟩
    have checked := (CoverVerification.verifier_decides.2 _).mp accepted
    change CoverVerification.verify (Encoding.pairWords input bits)=true at checked
    rw [CoverVerification.verify_pairWords] at checked
    cases decoded : X3CEncoding.codec.decodeExact input with
    | none => simp [CoverVerification.checkEncodedMask,decoded] at checked
    | some instanceData =>
      exact ⟨instanceData,decoded,(CoverVerification.yes_iff_mask instanceData).mpr
        ⟨bits,by simpa [CoverVerification.checkEncodedMask,decoded] using checked⟩⟩

/-- X3C is NP-complete for the explicit-universe canonical encoding,
through concrete polynomial-time generators and a concrete verifier. -/
theorem X3C_NPComplete : Complexity.NPComplete X3CLanguage := ⟨X3C_NP,X3C_NPHard⟩

end Counting.External.CoverMachine
