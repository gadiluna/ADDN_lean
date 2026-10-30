import Counting.ExternalCNFEntryBounds
import Counting.ExternalSATMachine
import Counting.ComplexityComposition

namespace Counting.External.CNFMachine
open StackMachine

/-- The canonical finite workspace has physical input register zero and
physical output register one. -/
def canonicalWorkspace : ClauseWorkspace 0 := Function.Embedding.refl _

def stackGenerator : Program := (entryRoutine 0 canonicalWorkspace).program

/-- All input strings are handled by the same executable program; malformed
syntax produces the fixed negative instance. -/
theorem stackGenerator_computes : ComputesIn stackGenerator reduceThreeSAT
    (Complexity.polynomial entryCoefficient 7) := by
  intro input
  let initialStore := (initial stackGenerator input).store
  have empty (i : Fin 52) (different : i≠0) : initialStore (canonicalWorkspace i)=[] := by
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

/-- The compiler pays every simulation and cleanup transition and leaves
the entire tape equal to the canonical output word. -/
theorem machineGenerator_computesCleanIn : Complexity.ComputesCleanIn machineGenerator reduceThreeSAT
    (Complexity.polynomial (20*(entryCoefficient+55)^2) 16) :=
  Compiler.computesCleanIn_polynomial entryCoefficient 7 stackGenerator_computes

/-- Polynomial-time SAT-to-three-SAT reduction in the fixed Turing model. -/
theorem SAT_reduces_ThreeSAT : Complexity.ManyOnePoly CookLevin.SAT ThreeSATLanguage :=
  ⟨reduceThreeSAT,machineGenerator,20*(entryCoefficient+55)^2,16,machineGenerator_computesCleanIn,
    fun input=>(reduceThreeSAT_yes_iff input).symm⟩

theorem ThreeSAT_NPHard : Complexity.NPHard ThreeSATLanguage :=
  CookLevin.SAT_NPHard.of_reduction SAT_reduces_ThreeSAT

end Counting.External.CNFMachine
