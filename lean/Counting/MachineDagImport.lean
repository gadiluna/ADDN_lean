import Counting.StackDagImportCompleteBounds
import Counting.StackCompilerComplete

namespace Counting.Machine
open StackMachine.DagUpdate.Import

def dagImportProgram : Program := StackMachine.Compiler.compile completeImport.program

/-- A concrete physical machine imports compact node tables, returns the
new pool and complete reference map, and leaves the whole output tape clean.
Canonical encodings are the only input premise: graph validity, ordered
edges, positive multiplicities and distinct nodes are not required. -/
theorem dagImport_clean (pool : Array Executable.Node) (nodes : List Executable.Node) :
    ∃ time output,
      time ≤ (20*(completeImportCoefficient+99)^2)*((importInput pool nodes).length+1)^30 ∧
      HaltsAt dagImportProgram (importInput pool nodes) time output ∧
      output.tape.denotes=Turing.Tape.mk₁ ((importOutput pool nodes).map bitSymbol) := by
  obtain ⟨steps,last,bounded,halted,stored⟩ := completeImport_halts pool nodes
  obtain ⟨time,output,timeBound,executed,tape⟩ := StackMachine.Compiler.compile_halts halted
  refine ⟨time,output,timeBound.trans ?_,executed,?_⟩
  · let size := (importInput pool nodes).length
    have linear : size+1 ≤ (size+1)^15 := Nat.le_self_pow (by decide) _
    have positive : 1 ≤ (size+1)^15 := Nat.one_le_pow' 15 size
    have base : size+94+steps+4 ≤ (completeImportCoefficient+99)*(size+1)^15 := by
      change steps ≤ completeImportCoefficient*(size+1)^15 at bounded
      simp only [Nat.add_mul]
      omega
    calc
      _ ≤ 20*((completeImportCoefficient+99)*(size+1)^15)^2 :=
        Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left base 2)
      _ = _ := by ring
  · rw [stored] at tape
    exact tape

theorem dagImport_exact (pool : Array Executable.Node) (vista : Executable.Vista) :
    importOutput pool vista.nodes.toList=
      (Encoding.product (Encoding.array Encoding.node) (Encoding.array Encoding.natural)).encode
        (Executable.importVista pool vista) := by
  simp only [importOutput,fold_importVista]

end Counting.Machine
