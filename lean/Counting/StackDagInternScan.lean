import Counting.StackDagInternScanSpec
import Counting.StackDagInternHeader
import Counting.StackDagParentBounds

namespace Counting.StackMachine.DagUpdate.Intern
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def scan : Routine 30 := sequence readHeader loop

def searchResult (store : Store 30) (query : Executable.Node) (nodes : List Executable.Node)
    (suffix : List Bool) : Store 30 :=
  let result := Executable.firstIndex query nodes
  Function.update (Function.update (Function.update store 0 suffix) 19 [result.isSome]) 18
    (List.replicate (result.getD nodes.length) true)

/-- Complete first-occurrence search over a compact node table, with the
binary list header read and bounded by its physical payload. -/
theorem scan_executes (store : Store 30) (query : Executable.Node)
    (nodes : List Executable.Node) (suffix : List Bool)
    (source : store 0=(Encoding.list Encoding.node).encode nodes++suffix)
    (queryAt : store 17=(Encoding.node.encode query).reverse)
    (status : store 1=[true]) (foundAt : store 19=[false]) (indexAt : store 18=[])
    (empty : ∀ r : Fin 32,(2 ≤ r.val ∧ r.val ≤ 16) ∨ (20 ≤ r.val ∧ r.val ≤ 24) → store r=[]) :
    ∃ time ≤ 5000*((store 0).length+(store 17).length+1)^4,
      Executes scan store time (searchResult store query nodes suffix) := by
  obtain ⟨headerTime,headerBound,headerRun⟩ := readHeader_executes store nodes suffix source status (by
    intro r member
    apply empty
    rcases member with first|last
    · exact Or.inl first
    · subst r;right;decide)
  let ready := Function.update (Function.update store 0 (Encoding.sequence Encoding.node nodes++suffix)) 24
    (List.replicate nodes.length true)
  have tailBound : (ready 0).length ≤ (store 0).length := by
    simp only [ready,Function.update_of_ne (show (0:Fin 32)≠24 by decide),Function.update_self]
    rw [source]
    simp only [Encoding.list,List.length_append]
    omega
  have work (r : Fin 32) (member : (2 ≤ r.val ∧ r.val ≤ 16) ∨ (20 ≤ r.val ∧ r.val ≤ 23)) : ready r=[] := by
    have n0 : r≠0 := by intro equal;subst r;norm_num at member
    have n24 : r≠24 := by intro equal;subst r;norm_num at member
    have original : store r=[] := empty r (by omega)
    simp [ready,n0,n24,original]
  obtain ⟨loopTime,loopBound,loopRun⟩ := loop_executes ready query nodes false 0 suffix (store 0).length
    (by simp [ready]) (by simp [ready,queryAt]) (by simp [ready,status])
    (by simp [ready,foundAt]) (by simp [ready,indexAt]) (by simp [ready]) work tailBound
  have final : scanned ready query nodes false 0 suffix=searchResult store query nodes suffix := by
    funext r
    rw [scanned,scanState_firstIndex]
    by_cases r0 : r=0 <;> by_cases r18 : r=18 <;> by_cases r19 : r=19 <;> by_cases r24 : r=24 <;>
      simp [ready,searchResult,r0,r18,r19,r24,empty]
  rw [final] at loopRun
  refine ⟨headerTime+1+loopTime,?_,headerRun.sequence loopRun⟩
  have nodesBound : nodes.length ≤ (store 0).length := by
    have count := DagValidation.node_sequence_count_le nodes
    rw [source]
    simp only [Encoding.list,List.length_append]
    omega
  have queryLength : (store 17).length=(Encoding.node.encode query).length := by
    rw [queryAt,List.length_reverse]
  rw [←queryLength] at loopBound
  let K := (store 0).length+(store 17).length+1
  have positive : 1 ≤ K := by omega
  have nodesK : nodes.length ≤ K := by omega
  have loopK := (Nat.mul_le_mul_right (3000*K^3+2) nodesK)
  have headerK := Nat.pow_le_pow_left (show (store 0).length+1 ≤ K by omega) 3
  have k1 : K ≤ K^4 := Nat.le_self_pow (by decide) _
  have k3 : K^3 ≤ K^4 := pow_le_pow_right₀ positive (by decide)
  have one : 1 ≤ K^4 := one_le_pow₀ positive
  change _ ≤ 5000*K^4
  change loopTime ≤ nodes.length*(3000*K^3+2)+1 at loopBound
  have power : K*K^3=K^4 := by ring
  nlinarith only [headerBound,loopBound,loopK,headerK,k1,k3,one,power]

end Counting.StackMachine.DagUpdate.Intern
