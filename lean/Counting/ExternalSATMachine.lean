import Counting.ExternalSATEntry
import Counting.ExternalCookLevinMachine
import Counting.MachineBooleanDecision

namespace Counting.External.SATVerification
open StackMachine

/-- The physical input is role 28 and the single Boolean output is role 1. -/
def canonicalWorkspace : SATWorkspace 0 :=
  ⟨![28,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,0,29,30,31],by decide⟩

def stackVerifier : Program := (entryRoutine 0 canonicalWorkspace).program

/-- A total executable verifier, including every malformed input string. -/
theorem stackVerifier_computes : ComputesIn stackVerifier (fun input => [verify input])
    (Complexity.polynomial verifierCoefficient 5) := by
  intro input
  let initialStore := (initial stackVerifier input).store
  have empty : ∀ i : Fin 32,i≠28 → initialStore (canonicalWorkspace i)=[] := by
    intro i different
    have ne : canonicalWorkspace i≠0 := by
      intro same
      exact different (canonicalWorkspace.injective (same.trans (show 0=canonicalWorkspace 28 from rfl)))
    change (if canonicalWorkspace i=(0:Fin 32) then input else [])=[]
    exact if_neg ne
  obtain ⟨time,bound,result,execution,output⟩ := entryRoutine_executes 0 canonicalWorkspace initialStore empty
  have source : initialStore (canonicalWorkspace 28)=input := rfl
  rw [source] at bound output
  obtain ⟨finish,ran,halted,finalStore⟩ := execution
  refine ⟨time,finish,bound,⟨ran,halted⟩,?_⟩
  rw [finalStore]
  exact output

def transducer : Machine.Program := Compiler.compile stackVerifier

theorem transducer_computesCleanIn : Complexity.ComputesCleanIn transducer (fun input => [verify input])
    (Complexity.polynomial (20*(verifierCoefficient+35)^2) 12) :=
  Compiler.computesCleanIn_polynomial verifierCoefficient 5 stackVerifier_computes

/-- Acceptance reads the produced bit in a charged physical transition. -/
def verifier : Machine.Program := Machine.compose transducer Machine.booleanDecision

def timeCoefficient := Complexity.compositionCoefficient (20*(verifierCoefficient+35)^2) 1 0

def timeExponent := Complexity.compositionExponent 12 0

theorem verifier_decides : Complexity.DecidesIn verifier {input | verify input=true}
    (Complexity.polynomial timeCoefficient timeExponent) :=
  transducer_computesCleanIn.boolean_decides

end Counting.External.SATVerification

namespace Counting.External.CookLevin

/-- Membership uses an explicit truth-assignment word, bounded by the
encoded variable table, and the concrete total Turing verifier above. -/
theorem SAT_NP : Complexity.NP SAT := by
  refine ⟨SATVerification.verifier,SATVerification.timeCoefficient,SATVerification.timeExponent,1,1,
    SATVerification.verifier_decides.1,?_⟩
  intro input
  constructor
  · intro member
    obtain ⟨bits,bound,accepted⟩ := SATVerification.exists_check_iff input |>.mp member
    refine ⟨bits,?_,?_⟩
    · simpa only [Complexity.polynomial,pow_one,one_mul] using bound.trans (Nat.le_succ _)
    · apply (SATVerification.verifier_decides.2 _).mpr
      change SATVerification.verify (Encoding.pairWords input bits)=true
      rwa [SATVerification.verify_pairWords]
  · rintro ⟨bits,_bound,accepted⟩
    have checked := (SATVerification.verifier_decides.2 _).mp accepted
    change SATVerification.verify (Encoding.pairWords input bits)=true at checked
    rw [SATVerification.verify_pairWords] at checked
    exact SATVerification.check_sound input bits checked

/-- Cook--Levin completeness in the fixed finite-alphabet Turing model,
with verified polynomial runtime for both generator and verifier. -/
theorem SAT_NPComplete : Complexity.NPComplete SAT := ⟨SAT_NP,SAT_NPHard⟩

end Counting.External.CookLevin
