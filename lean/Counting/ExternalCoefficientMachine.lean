import Counting.ExternalCoefficientEntryBounds
import Counting.StackCompilerComplete

namespace Counting.External.CoefficientMachine
open StackMachine

def canonicalWorkspace : Workspace 0 := Function.Embedding.refl _
def stackGenerator : Program := (entryRoutine 0 canonicalWorkspace).program

theorem stackGenerator_computes : ComputesIn stackGenerator computeCoefficients
    (Complexity.polynomial entryCoefficient 8) := by
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

/-- The actual finite-state tape machine computes the binary coefficient
list on every bitword. Invalid X3C inputs map to the empty list; all copies,
parsing, powers, additions, framing and tape cleanup are charged. -/
theorem machineGenerator_computesCleanIn : Complexity.ComputesCleanIn machineGenerator computeCoefficients
    (Complexity.polynomial (20*(entryCoefficient+67)^2) 18) :=
  Compiler.computesCleanIn_polynomial entryCoefficient 8 stackGenerator_computes

end Counting.External.CoefficientMachine
