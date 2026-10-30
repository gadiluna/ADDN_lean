import Counting.ExternalMatchingEntryBounds
import Counting.ExternalCNFMachine

namespace Counting.External.MatchingMachine
open StackMachine

def canonicalWorkspace : GeneratorWorkspace 0 := Function.Embedding.refl _
def stackGenerator : Program := (entryRoutine 0 canonicalWorkspace).program

theorem stackGenerator_computes : ComputesIn stackGenerator reduceMatching
    (Complexity.polynomial entryCoefficient 9) := by
  intro input
  let initialStore := (initial stackGenerator input).store
  have empty (i : Fin 64) (different : i≠0) : initialStore (canonicalWorkspace i)=[] := by
    change (if i=0 then input else [])=[]
    exact if_neg different
  obtain ⟨time,bounded,result,execution,output⟩ := entryRoutine_executes 0 canonicalWorkspace initialStore empty
  have source : initialStore (canonicalWorkspace 0)=input := rfl
  rw [source] at bounded output
  obtain ⟨finish,ran,halted,finalStore⟩ := execution
  refine ⟨time,finish,bounded.trans (entryCost_polynomial input),⟨ran,halted⟩,?_⟩
  rw [finalStore]
  exact output

def machineGenerator : Machine.Program := Compiler.compile stackGenerator

/-- The entire output tape is clean, and all inputs, including malformed
encodings and canonical formulas of the wrong clause size, terminate. -/
theorem machineGenerator_computesCleanIn : Complexity.ComputesCleanIn machineGenerator reduceMatching
    (Complexity.polynomial (20*(entryCoefficient+67)^2) 20) :=
  Compiler.computesCleanIn_polynomial entryCoefficient 9 stackGenerator_computes

theorem ThreeSAT_reduces_ThreeDM : Complexity.ManyOnePoly CNFMachine.ThreeSATLanguage ThreeDMEncoding.MatchingLanguage :=
  ⟨reduceMatching,machineGenerator,20*(entryCoefficient+67)^2,20,machineGenerator_computesCleanIn,
    fun input=>(reduceMatching_yes_iff input).symm⟩

theorem ThreeDM_NPHard : Complexity.NPHard ThreeDMEncoding.MatchingLanguage :=
  CNFMachine.ThreeSAT_NPHard.of_reduction ThreeSAT_reduces_ThreeDM

end Counting.External.MatchingMachine
