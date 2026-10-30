import Counting.ExternalCoverEntryBounds
import Counting.ExternalMatchingMachine

namespace Counting.External.CoverMachine
open StackMachine MatchingMachine

def canonicalWorkspace : GeneratorWorkspace 0 := Function.Embedding.refl _
def stackGenerator : Program := (entryRoutine 0 canonicalWorkspace).program

theorem stackGenerator_computes : ComputesIn stackGenerator reduceCover
    (Complexity.polynomial entryCoefficient 5) := by
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

/-- A total clean-tape transducer, including malformed matching encodings.
The explicit universe controls the work on every binary coordinate. -/
theorem machineGenerator_computesCleanIn : Complexity.ComputesCleanIn machineGenerator reduceCover
    (Complexity.polynomial (20*(entryCoefficient+67)^2) 12) :=
  Compiler.computesCleanIn_polynomial entryCoefficient 5 stackGenerator_computes

def X3CLanguage : Complexity.Language := {word | X3CEncoding.BinaryX3C word}

theorem ThreeDM_reduces_X3C : Complexity.ManyOnePoly ThreeDMEncoding.MatchingLanguage X3CLanguage :=
  ⟨reduceCover,machineGenerator,20*(entryCoefficient+67)^2,12,machineGenerator_computesCleanIn,
    fun input=>(reduceCover_yes_iff input).symm⟩

theorem X3C_NPHard : Complexity.NPHard X3CLanguage :=
  MatchingMachine.ThreeDM_NPHard.of_reduction ThreeDM_reduces_X3C

end Counting.External.CoverMachine
