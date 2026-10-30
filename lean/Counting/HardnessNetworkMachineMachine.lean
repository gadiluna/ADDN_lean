import Counting.HardnessNetworkMachineEntryBounds
import Counting.StackCompilerComplete

namespace Counting.HardnessNetworkMachine
open StackMachine
set_option backward.isDefEq.respectTransparency false

def stackNetworkGenerator : Program := networkEntry.program

theorem stackNetworkGenerator_computes : ComputesIn stackNetworkGenerator networkTransform
    (Complexity.polynomial networkEntryCoefficient 9) := by
  intro input
  let initialStore : Routine.Store 94 := (initial stackNetworkGenerator input).store
  have empty (i : Fin 96) (different : i≠0) : initialStore i=[] := by
    change (if i=0 then input else [])=[]
    exact if_neg different
  obtain ⟨time,bounded,result,execution,output⟩:=networkEntry_executes initialStore empty
  have source : initialStore 0=input := rfl
  rw [source] at bounded output
  obtain ⟨finish,ran,halted,finalStore⟩:=execution
  refine ⟨time,finish,bounded.trans (networkEntryCost_polynomial input),⟨ran,halted⟩,?_⟩
  rw [finalStore]
  exact output

def networkMachine : Machine.Program := Compiler.compile stackNetworkGenerator

/-- A total finite-state tape transducer computes every multiplicity and
all row, matrix and round headers. Its final whole tape contains only the
serialized network; malformed X3C source words return the empty word. -/
theorem networkMachine_computesCleanIn : Complexity.ComputesCleanIn networkMachine networkTransform
    (Complexity.polynomial (20*(networkEntryCoefficient+99)^2) 20) :=
  Compiler.computesCleanIn_polynomial networkEntryCoefficient 9 stackNetworkGenerator_computes

end Counting.HardnessNetworkMachine
