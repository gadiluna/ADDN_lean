import Counting.StackDagImportComplete
import Counting.StackDagImportPolynomial

namespace Counting.StackMachine.DagUpdate.Import
open Routine

def completeImportCoefficient : Nat := importCoefficient*2^15+200

theorem completeImportBudget_polynomial (pool : Array Executable.Node) (nodes : List Executable.Node) :
    completeImportBudget pool nodes ≤ completeImportCoefficient*((importInput pool nodes).length+1)^15 := by
  let P := ((Encoding.array Encoding.node).encode pool).length
  let S := ((Encoding.list Encoding.node).encode nodes).length
  let K := (importInput pool nodes).length+1
  let R := ((Encoding.array Encoding.node).encode (nodes.foldl advance (pool,#[])).1).length
  have inputSize : (importInput pool nodes).length=2*P+1+S := by
    simp only [importInput,List.length_append,Encoding.frame_length,P,S]
  have positive : 1 ≤ K := by dsimp only [K];omega
  have poolBound : P ≤ K := by dsimp only [K];omega
  have sourceBound : S ≤ K := by dsimp only [K];omega
  have originalBound : P+S+1 ≤ K := by dsimp only [K];omega
  have output := (Executable.importFold_encoded_polynomial pool nodes).1
  change R ≤ 20*(P+S+1)^2 at output
  have outputBound := output.trans (Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left originalBound 2))
  have body := importNodesBudget_polynomial pool nodes S
  have bodyBase : P+S+S+1 ≤ 2*K := by dsimp only [K];omega
  have bodyBound : importNodesBudget pool nodes S ≤ (importCoefficient*2^15)*K^15 := by
    calc
      _ ≤ importCoefficient*(P+S+S+1)^15 := body
      _ ≤ importCoefficient*(2*K)^15 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left bodyBase 15)
      _ = _ := by ring
  have square : K^2 ≤ K^15 := Nat.pow_le_pow_right positive (by decide)
  have linear : K ≤ K^15 := Nat.le_self_pow (by decide) _
  have one : 1 ≤ K^15 := one_le_pow₀ positive
  change completeImportBudget pool nodes ≤ completeImportCoefficient*K^15
  change 5*P+6*S+importNodesBudget pool nodes S+6*R+18 ≤ _
  unfold completeImportCoefficient
  nlinarith only [poolBound,sourceBound,outputBound,bodyBound,square,linear,one]

theorem completeImport_polynomial (pool : Array Executable.Node) (nodes : List Executable.Node) :
    ∃ time ≤ completeImportCoefficient*((importInput pool nodes).length+1)^15,
      Executes completeImport (inputStore 94 (importInput pool nodes)) time
        (outputStore 94 (importOutput pool nodes)) := by
  obtain ⟨time,bound,ran⟩ := completeImport_executes pool nodes
  exact ⟨time,bound.trans (completeImportBudget_polynomial pool nodes),ran⟩

theorem completeImport_halts (pool : Array Executable.Node) (nodes : List Executable.Node) :
    ∃ time last,time ≤ completeImportCoefficient*((importInput pool nodes).length+1)^15 ∧
      HaltsAt completeImport.program (importInput pool nodes) time last ∧
      last.store 1=importOutput pool nodes := by
  obtain ⟨time,bound,last,ran,halted,stored⟩ := completeImport_polynomial pool nodes
  exact ⟨time,last,bound,⟨ran,halted⟩,by rw [stored];rfl⟩

end Counting.StackMachine.DagUpdate.Import
