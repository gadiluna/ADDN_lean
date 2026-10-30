import Counting.ExternalCoverNormalizeEntryBounds
import Counting.StackCompilerComplete

namespace Counting.External.CoverNormalization
open StackMachine

def canonicalWorkspace : MatchingMachine.GeneratorWorkspace 0 := Function.Embedding.refl _
def stackGenerator : Program := (entryRoutine 0 canonicalWorkspace).program

theorem stackGenerator_computes : ComputesIn stackGenerator normalizeWord
    (Complexity.polynomial entryCoefficient 5) := by
  intro input
  let initialStore:=(initial stackGenerator input).store
  have empty (i : Fin 64) (different : i≠0) : initialStore (canonicalWorkspace i)=[] := by
    change (if i=0 then input else [])=[]
    exact if_neg different
  obtain ⟨time,bounded,result,execution,output⟩:=entryRoutine_executes 0 canonicalWorkspace initialStore empty
  have source : initialStore (canonicalWorkspace 0)=input := rfl
  rw [source] at bounded output
  obtain ⟨finish,ran,halted,finalStore⟩:=execution
  refine ⟨time,finish,bounded.trans (entryCost_polynomial input),⟨ran,halted⟩,?_⟩
  rw [finalStore]
  exact output

def machineGenerator : Machine.Program := Compiler.compile stackGenerator

/-- The fixed finite-alphabet tape machine normalizes every binary input.
Invalid sources map to a fixed negative normalized X3C instance. Parsing,
first-occurrence deduplication, padding, headers and tape cleanup are charged. -/
theorem machineGenerator_computesCleanIn : Complexity.ComputesCleanIn machineGenerator normalizeWord
    (Complexity.polynomial (20*(entryCoefficient+67)^2) 12) :=
  Compiler.computesCleanIn_polynomial entryCoefficient 5 stackGenerator_computes

end Counting.External.CoverNormalization
