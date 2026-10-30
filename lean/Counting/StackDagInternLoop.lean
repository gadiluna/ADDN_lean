import Counting.StackDagInternStep

namespace Counting.StackMachine.DagUpdate.Intern
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def scanState (query : Executable.Node) : List Executable.Node → Bool → Nat → Bool×Nat
  | [],found,index => (found,index)
  | node::rest,found,index =>
      let next := found || decide (query=node)
      scanState query rest next (if next then index else index+1)

abbrev loop : Routine 30 := forEach 24 step

def scanned (store : Store 30) (query : Executable.Node) (nodes : List Executable.Node)
    (found : Bool) (index : Nat) (suffix : List Bool) : Store 30 :=
  let result := scanState query nodes found index
  Function.update (Function.update (Function.update (Function.update store 0 suffix) 24 [])
    19 [result.1]) 18 (List.replicate result.2 true)

/-- The index counts only nodes before the first match, and is bounded by
the explicit node sequence. Every node is parsed and compared physically. -/
theorem loop_executes (store : Store 30) (query : Executable.Node)
    (nodes : List Executable.Node) (found : Bool) (index : Nat) (suffix : List Bool) (L : Nat)
    (source : store 0=Encoding.sequence Encoding.node nodes++suffix)
    (queryAt : store 17=(Encoding.node.encode query).reverse)
    (status : store 1=[true]) (foundAt : store 19=[found])
    (indexAt : store 18=List.replicate index true)
    (counter : store 24=List.replicate nodes.length true)
    (empty : ∀ r : Fin 32,(2 ≤ r.val ∧ r.val ≤ 16) ∨ (20 ≤ r.val ∧ r.val ≤ 23) → store r=[])
    (sourceLimit : (store 0).length ≤ L) :
    ∃ time ≤ nodes.length*(3000*(L+(Encoding.node.encode query).length+1)^3+2)+1,
      Executes loop store time (scanned store query nodes found index suffix) := by
  induction nodes generalizing store found index with
  | nil =>
    have counterEmpty : store 24=[] := by simpa using counter
    have sourceAt : store 0=suffix := by simpa [Encoding.sequence] using source
    obtain ⟨ran,halted⟩ := repeat_empty (24:Fin 32) step store counterEmpty
    have final : scanned store query [] found index suffix=store := by
      funext r
      by_cases r0 : r=0 <;> by_cases r18 : r=18 <;> by_cases r19 : r=19 <;> by_cases r24 : r=24 <;>
        simp [scanned,scanState,r0,r18,r19,r24,sourceAt,counterEmpty,indexAt,foundAt]
    exact ⟨1,by simp,⟨1,store⟩,ran,halted,final.symm⟩
  | cons node nodes ih =>
    let consumed := Function.update store 24 (List.replicate nodes.length true)
    have consumedEmpty (r : Fin 32) (member : (2 ≤ r.val ∧ r.val ≤ 16) ∨ (20 ≤ r.val ∧ r.val ≤ 23)) : consumed r=[] := by
      have ne : r≠24 := by intro equal;subst r;norm_num at member
      simp [consumed,ne,empty r member]
    obtain ⟨bodyTime,bodyBound,bodyFinish,bodyRun,bodyHalt,bodyStore⟩ := step_executes consumed query node found
      (Encoding.sequence Encoding.node nodes++suffix)
      (by simpa [consumed,Encoding.sequence,List.append_assoc] using source)
      (by simp [consumed,queryAt]) (by simp [consumed,status]) (by simp [consumed,foundAt]) consumedEmpty
    let next := found || decide (query=node)
    let nextIndex := if next then index else index+1
    let middle := stepped consumed query node found (Encoding.sequence Encoding.node nodes++suffix)
    have middleEmpty (r : Fin 32) (member : (2 ≤ r.val ∧ r.val ≤ 16) ∨ (20 ≤ r.val ∧ r.val ≤ 23)) : middle r=[] := by
      have n0 : r≠0 := by intro equal;subst r;norm_num at member
      have n18 : r≠18 := by intro equal;subst r;norm_num at member
      have n19 : r≠19 := by intro equal;subst r;norm_num at member
      simp [middle,stepped,n0,n18,n19,consumedEmpty r member]
    have middleIndex : middle 18=List.replicate nextIndex true := by
      change (if next then consumed 18 else true::consumed 18)=
        List.replicate (if next then index else index+1) true
      have current : consumed 18=List.replicate index true := by simp [consumed,indexAt]
      rw [current]
      cases next <;> simp [List.replicate_succ]
    have tailSize : (middle 0).length ≤ L := by
      have inputLength : (store 0).length=(Encoding.node.encode node).length+
          (Encoding.sequence Encoding.node nodes++suffix).length := by
        rw [source]
        simp [Encoding.sequence,List.length_append]
      simp only [middle,stepped,Function.update_of_ne (show (0:Fin 32)≠18 by decide),
        Function.update_of_ne (show (0:Fin 32)≠19 by decide),Function.update_self]
      omega
    obtain ⟨tailTime,tailBound,tailFinish,tailRun,tailHalt,tailStore⟩ := ih middle next nextIndex
      (by simp [middle,stepped]) (by simp [middle,stepped,consumed,queryAt])
      (by simp [middle,stepped,consumed,status]) (by simp [middle,stepped,next])
      middleIndex (by simp [middle,stepped,consumed]) middleEmpty tailSize
    have firstRun := repeat_iteration (24:Fin 32) step store true (List.replicate nodes.length true)
      (by simpa only [List.length_cons,List.replicate_succ] using counter) bodyTime bodyFinish bodyRun bodyHalt
    have final : scanned middle query nodes next nextIndex suffix=
        scanned store query (node::nodes) found index suffix := by
      funext r
      by_cases r0 : r=0 <;> by_cases r18 : r=18 <;> by_cases r19 : r=19 <;> by_cases r24 : r=24 <;>
        simp [scanned,scanState,middle,stepped,consumed,next,nextIndex,r0,r18,r19,r24]
    refine ⟨bodyTime+2+tailTime,?_,tailFinish,?_,tailHalt,tailStore.trans final⟩
    · have inputSame : consumed 0=store 0 := by simp [consumed]
      have querySame : (consumed 17).length=(Encoding.node.encode query).length := by
        simp [consumed,queryAt]
      rw [inputSame,querySame] at bodyBound
      have bounded : bodyTime ≤ 3000*(L+(Encoding.node.encode query).length+1)^3 :=
        bodyBound.trans (Nat.mul_le_mul_left 3000 (Nat.pow_le_pow_left (by omega) 3))
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
    · rw [Machine.run_add,firstRun,Option.bind_some,bodyStore]
      exact tailRun

end Counting.StackMachine.DagUpdate.Intern
