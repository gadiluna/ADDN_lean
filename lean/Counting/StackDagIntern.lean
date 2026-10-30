import Counting.StackDagInternPool

namespace Counting.StackMachine.DagUpdate.Intern
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

def internNode : Routine 62 := sequence searchTable
  (sequence selectPool (ofProgram (Unary.toBinaryProgram 61 22 3 4)))

theorem intern_index_first (nodes : List Executable.Node) (query : Executable.Node) :
    (Executable.intern nodes.toArray query).2=(Executable.firstIndex query nodes).getD nodes.length := by
  rw [Executable.intern_toArray]
  cases Executable.firstIndex query nodes <;> rfl

/-- Execute structural interning on the actual serialized node table.
The first exact match is reused; otherwise the node is appended. Only the
two output registers change, and the returned index is a binary numeral. -/
theorem internNode_executes (store : Store 62) (nodes : List Executable.Node) (query : Executable.Node)
    (source : store 0=(Encoding.list Encoding.node).encode nodes)
    (queryAt : store 1=Encoding.node.encode query)
    (empty : ∀ r : Fin 64,2 ≤ r.val → r.val ≤ 37 → store r=[]) :
    ∃ time ≤ 8000*((store 0).length+(store 1).length+1)^4,
      Executes internNode store time
        (Function.update (Function.update store 2
          ((Encoding.array Encoding.node).encode (Executable.intern nodes.toArray query).1))
          3 (Executable.intern nodes.toArray query).2.bits) := by
  obtain ⟨searchTime,searchBound,searchRun⟩ := searchTable_executes store nodes query source queryAt
    (fun r lower upper=>empty r (by omega) upper)
  let ready := searched store query nodes
  obtain ⟨poolTime,poolBound,poolRun⟩ := selectPool_executes ready nodes query
    (by simp [ready,searched,source]) (by simp [ready,searched,queryAt])
    (by simp [ready,searched]) (by simp [ready,searched])
    (by simp [ready,searched,empty]) (by
      intro r lower upper
      have n22 : r≠22 := by intro eq;subst r;norm_num at upper
      have n23 : r≠23 := by intro eq;subst r;norm_num at upper
      simp [ready,searched,n22,n23,empty r (by omega) (by omega)])
  let updated := Function.update (Function.update ready 23 []) 2
    ((Encoding.array Encoding.node).encode (Executable.intern nodes.toArray query).1)
  let index := (Executable.firstIndex query nodes).getD nodes.length
  obtain ⟨binaryTime,binaryBound,binaryRun⟩ := toBinary_executes 61 (22:Fin 64) 3 4
    (by decide) (by decide) (by decide) updated 0
    (by simp [updated,ready,searched,empty]) (by simp [updated,ready,searched,empty])
  have indexValue : updated 22=List.replicate index true := by simp [updated,ready,searched,index]
  rw [indexValue,List.length_replicate,Nat.zero_add] at binaryRun binaryBound
  have final : Function.update (Function.update updated 22 []) 3 index.bits=
      Function.update (Function.update store 2
        ((Encoding.array Encoding.node).encode (Executable.intern nodes.toArray query).1))
        3 (Executable.intern nodes.toArray query).2.bits := by
    rw [intern_index_first]
    funext r
    fin_cases r <;> simp [updated,ready,searched,index,empty]
  rw [final] at binaryRun
  refine ⟨_,?_,searchRun.sequence (poolRun.sequence binaryRun)⟩
  have sourceSame : ready 0=store 0 := by simp [ready,searched]
  have querySame : ready 1=store 1 := by simp [ready,searched]
  rw [sourceSame,querySame] at poolBound
  have nodesBound : nodes.length ≤ (store 0).length := by
    have count := DagValidation.node_sequence_count_le nodes
    rw [source]
    simp only [Encoding.list,List.length_append]
    omega
  have indexBound := firstIndex_getD_le_length query nodes
  change index ≤ nodes.length at indexBound
  let K := (store 0).length+(store 1).length+1
  have positive : 1 ≤ K := by omega
  have indexK : index ≤ K := by omega
  have nextK : index+1 ≤ K := by omega
  have multiplication := Nat.mul_le_mul indexK nextK
  have square : K^2 ≤ K^4 := pow_le_pow_right₀ positive (by decide)
  have one : 1 ≤ K^4 := one_le_pow₀ positive
  change searchTime ≤ 6000*K^4 at searchBound
  change poolTime ≤ 1000*K^2 at poolBound
  change _ ≤ 8000*K^4
  nlinarith only [binaryBound,multiplication,square,one,searchBound,poolBound]

theorem internNode_executes_array (store : Store 62) (nodes : Array Executable.Node) (query : Executable.Node)
    (source : store 0=(Encoding.array Encoding.node).encode nodes)
    (queryAt : store 1=Encoding.node.encode query)
    (empty : ∀ r : Fin 64,2 ≤ r.val → r.val ≤ 37 → store r=[]) :
    ∃ time ≤ 8000*((store 0).length+(store 1).length+1)^4,
      Executes internNode store time
        (Function.update (Function.update store 2
          ((Encoding.array Encoding.node).encode (Executable.intern nodes query).1))
          3 (Executable.intern nodes query).2.bits) := by
  simpa only [Array.toArray_toList] using internNode_executes store nodes.toList query source queryAt empty

end Counting.StackMachine.DagUpdate.Intern
