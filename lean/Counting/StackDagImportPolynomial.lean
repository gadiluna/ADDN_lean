import Counting.StackDagImportNodes
import Counting.StackDagImportBudgetBounds

namespace Counting.StackMachine.DagUpdate.Import
open Routine
set_option backward.isDefEq.respectTransparency false

theorem loopBudget_suffix_bound (pool : Array Executable.Node) (nodes : List Executable.Node)
    (sourceLength : Nat) (visited remaining : List Executable.Node)
    (partition : visited++remaining=nodes) :
    let state := visited.foldl advance (pool,#[])
    loopBudget state.2 state.1 remaining sourceLength ≤
      remaining.length*(importStepCoefficient*(((Encoding.array Encoding.node).encode pool).length+
        ((Encoding.list Encoding.node).encode nodes).length+sourceLength+1)^14+2)+1 := by
  induction remaining generalizing visited with
  | nil => simp [loopBudget]
  | cons node remaining ih =>
    let state := visited.foldl advance (pool,#[])
    have inside : visited.length < nodes.length := by
      rw [←partition,List.length_append,List.length_cons]
      omega
    have stateEq : Executable.importPrefixState pool nodes visited.length=state := by
      simp only [Executable.importPrefixState,←partition,List.take_left]
      rfl
    have nodeEq : nodes[visited.length]'inside=node := by simp [←partition]
    have first := stepBudget_prefix pool nodes visited.length sourceLength inside
    rw [stateEq,nodeEq] at first
    have tail := ih (visited++[node]) (by simpa only [List.append_assoc,List.singleton_append] using partition)
    have nextEq : (visited++[node]).foldl advance (pool,#[])=advance state node := by
      simp only [List.foldl_append,List.foldl_cons,List.foldl_nil,state]
    dsimp only at tail
    rw [nextEq] at tail
    change loopBudget state.2 state.1 (node::remaining) sourceLength ≤ _
    simp only [loopBudget,List.length_cons,Nat.add_mul,Nat.one_mul]
    change stepBudget state.2 state.1 node sourceLength+2+
      loopBudget (advance state node).2 (advance state node).1 remaining sourceLength ≤ _
    omega

theorem loopBudget_polynomial (pool : Array Executable.Node) (nodes : List Executable.Node)
    (sourceLength : Nat) :
    loopBudget #[] pool nodes sourceLength ≤
      (importStepCoefficient+3)*(((Encoding.array Encoding.node).encode pool).length+
        ((Encoding.list Encoding.node).encode nodes).length+sourceLength+1)^15 := by
  let K := ((Encoding.array Encoding.node).encode pool).length+
    ((Encoding.list Encoding.node).encode nodes).length+sourceLength+1
  have bound := loopBudget_suffix_bound pool nodes sourceLength [] nodes rfl
  simp only [List.foldl_nil] at bound
  change loopBudget #[] pool nodes sourceLength ≤ nodes.length*(importStepCoefficient*K^14+2)+1 at bound
  have count : nodes.length ≤ ((Encoding.list Encoding.node).encode nodes).length := by
    simpa only [Encoding.array,Encoding.transport,List.toList_toArray,List.size_toArray] using
      Encoding.array_size_le_length Encoding.node nodes.toArray (fun node _=>Encoding.node_positive_length node)
  have countK : nodes.length ≤ K := by dsimp only [K];omega
  have positive : 1 ≤ K := by dsimp only [K];omega
  have multiply := Nat.mul_le_mul_right (importStepCoefficient*K^14+2) countK
  have linear : K ≤ K^15 := Nat.le_self_pow (by decide) _
  have one : 1 ≤ K^15 := one_le_pow₀ positive
  have power : K*K^14=K^15 := by ring
  change _ ≤ (importStepCoefficient+3)*K^15
  nlinarith only [bound,multiply,linear,one,power]

def importCoefficient : Nat := importStepCoefficient+1830

/-- The full list importer has a polynomial bound in its original compact
source and pool; all intermediate pools and maps are bounded uniformly. -/
theorem importNodesBudget_polynomial (pool : Array Executable.Node) (nodes : List Executable.Node)
    (sourceLength : Nat) :
    importNodesBudget pool nodes sourceLength ≤
      importCoefficient*(((Encoding.array Encoding.node).encode pool).length+
        ((Encoding.list Encoding.node).encode nodes).length+sourceLength+1)^15 := by
  let K := ((Encoding.array Encoding.node).encode pool).length+
    ((Encoding.list Encoding.node).encode nodes).length+sourceLength+1
  have loopBound := loopBudget_polynomial pool nodes sourceLength
  change loopBudget #[] pool nodes sourceLength ≤ (importStepCoefficient+3)*K^15 at loopBound
  have positive : 1 ≤ K := by dsimp only [K];omega
  have base : sourceLength+1 ≤ K := by dsimp only [K];omega
  have header := Nat.pow_le_pow_left base 3
  have cubic : K^3 ≤ K^15 := Nat.pow_le_pow_right positive (by decide)
  have count : nodes.length ≤ ((Encoding.list Encoding.node).encode nodes).length := by
    simpa only [Encoding.array,Encoding.transport,List.toList_toArray,List.size_toArray] using
      Encoding.array_size_le_length Encoding.node nodes.toArray (fun node _=>Encoding.node_positive_length node)
  have countK : nodes.length ≤ K := by dsimp only [K];omega
  have linear : K ≤ K^15 := Nat.le_self_pow (by decide) _
  have one : 1 ≤ K^15 := one_le_pow₀ positive
  change importNodesBudget pool nodes sourceLength ≤ importCoefficient*K^15
  dsimp only [importNodesBudget,importCoefficient]
  nlinarith only [loopBound,header,cubic,countK,linear,one]

theorem importNodes_executes_polynomial (store : Store 94) (pool : Array Executable.Node)
    (nodes : List Executable.Node) (suffix : List Bool)
    (source : store 70=(Encoding.list Encoding.node).encode nodes++suffix)
    (poolAt : store 64=(Encoding.array Encoding.node).encode pool)
    (status : store 71=[true])
    (empty : ∀ r : Fin 96,(r.val ≤ 68 ∧ r≠64) ∨ r=72 ∨ r=73 → store r=[]) :
    ∃ time ≤ (importCoefficient*2^15)*((store 70).length+(store 64).length+1)^15,
      Executes importNodes store time (importResult store pool nodes suffix) := by
  obtain ⟨time,bound,ran⟩ := importNodes_executes store pool nodes suffix source poolAt status empty
  refine ⟨time,bound.trans ((importNodesBudget_polynomial pool nodes _).trans ?_),ran⟩
  have sourceBound : ((Encoding.list Encoding.node).encode nodes).length ≤ (store 70).length := by
    rw [source,List.length_append]
    omega
  have base : ((Encoding.array Encoding.node).encode pool).length+
      ((Encoding.list Encoding.node).encode nodes).length+(store 70).length+1 ≤
      2*((store 70).length+(store 64).length+1) := by rw [poolAt];omega
  calc
    _ ≤ importCoefficient*(2*((store 70).length+(store 64).length+1))^15 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left base 15)
    _ = _ := by ring

end Counting.StackMachine.DagUpdate.Import
