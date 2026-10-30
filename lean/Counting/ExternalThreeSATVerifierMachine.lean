import Counting.ExternalThreeSATVerifierEntry
import Counting.ExternalCNFMachine

namespace Counting.External.ThreeSATVerification
open StackMachine

def stackVerifier : Program := (entryRoutine 0 SATVerification.canonicalWorkspace).program

theorem stackVerifier_computes : ComputesIn stackVerifier (fun input => [verify input])
    (Complexity.polynomial verifierCoefficient 5) := by
  intro input
  let initialStore := (initial stackVerifier input).store
  have empty : ∀ i : Fin 32,i≠28 → initialStore (SATVerification.canonicalWorkspace i)=[] := by
    intro i different
    have ne : SATVerification.canonicalWorkspace i≠0 := by
      intro same
      exact different (SATVerification.canonicalWorkspace.injective
        (same.trans (show 0=SATVerification.canonicalWorkspace 28 from rfl)))
    change (if SATVerification.canonicalWorkspace i=(0:Fin 32) then input else [])=[]
    exact if_neg ne
  obtain ⟨time,bound,result,execution,output⟩ := entryRoutine_executes 0 SATVerification.canonicalWorkspace initialStore empty
  have source : initialStore (SATVerification.canonicalWorkspace 28)=input := rfl
  rw [source] at bound output
  obtain ⟨finish,ran,halted,finalStore⟩ := execution
  refine ⟨time,finish,bound,⟨ran,halted⟩,?_⟩
  rw [finalStore]
  exact output

def transducer : Machine.Program := Compiler.compile stackVerifier

theorem transducer_computesCleanIn : Complexity.ComputesCleanIn transducer (fun input => [verify input])
    (Complexity.polynomial (20*(verifierCoefficient+35)^2) 12) :=
  Compiler.computesCleanIn_polynomial verifierCoefficient 5 stackVerifier_computes

def verifier : Machine.Program := Machine.compose transducer Machine.booleanDecision
def timeCoefficient := Complexity.compositionCoefficient (20*(verifierCoefficient+35)^2) 1 0
def timeExponent := Complexity.compositionExponent 12 0

theorem verifier_decides : Complexity.DecidesIn verifier {input | verify input=true}
    (Complexity.polynomial timeCoefficient timeExponent) :=
  transducer_computesCleanIn.boolean_decides

end Counting.External.ThreeSATVerification

namespace Counting.External.CNFMachine

theorem ThreeSAT_NP : Complexity.NP ThreeSATLanguage := by
  refine ⟨ThreeSATVerification.verifier,ThreeSATVerification.timeCoefficient,ThreeSATVerification.timeExponent,1,1,
    ThreeSATVerification.verifier_decides.1,?_⟩
  intro input
  constructor
  · intro member
    obtain ⟨bits,bound,accepted⟩ := (ThreeSATVerification.exists_check_iff input).mp member
    refine ⟨bits,?_,?_⟩
    · simpa only [Complexity.polynomial,pow_one,one_mul] using bound.trans (Nat.le_succ _)
    · apply (ThreeSATVerification.verifier_decides.2 _).mpr
      change ThreeSATVerification.verify (Encoding.pairWords input bits)=true
      rwa [ThreeSATVerification.verify_pairWords]
  · rintro ⟨bits,_bound,accepted⟩
    have checked := (ThreeSATVerification.verifier_decides.2 _).mp accepted
    change ThreeSATVerification.verify (Encoding.pairWords input bits)=true at checked
    rw [ThreeSATVerification.verify_pairWords] at checked
    have sat : ThreeSATVerification.rawParser.exactEffect input=true ∧ SATVerification.check input bits=true := by
      simpa only [ThreeSATVerification.check,Bool.and_eq_true] using checked
    have witnessBound := SATVerification.check_witness_length input bits sat.2
    exact (ThreeSATVerification.exists_check_iff input).mpr ⟨bits,witnessBound,checked⟩

/-- Both directions of completeness use actual bounded machines on the
explicit-universe binary encoding and the exact three-occurrence grammar. -/
theorem ThreeSAT_NPComplete : Complexity.NPComplete ThreeSATLanguage := ⟨ThreeSAT_NP,ThreeSAT_NPHard⟩

end Counting.External.CNFMachine
