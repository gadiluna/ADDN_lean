import Counting.StackDagImportStep

namespace Counting.StackMachine.DagUpdate.Import
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

/-- The literal state transition used by `Executable.importVista`. -/
def advance (state : Array Executable.Node × Array Nat) (node : Executable.Node) :
    Array Executable.Node × Array Nat :=
  let result := Executable.intern state.1 (Executable.referenceMap state.2 node)
  (result.1,state.2.push result.2)

def loopBudget (mapping : Array Nat) (pool : Array Executable.Node) :
    List Executable.Node → Nat → Nat
  | [],_ => 1
  | node::nodes,L =>
      let next := advance (pool,mapping) node
      stepBudget mapping pool node L+2+loopBudget next.2 next.1 nodes L

abbrev loop : Routine 94 := forEach 73 step

def imported (store : Store 94) (mapping : Array Nat) (pool : Array Executable.Node)
    (nodes : List Executable.Node) (suffix : List Bool) : Store 94 :=
  let result := nodes.foldl advance (pool,mapping)
  Function.update (Function.update (Function.update (Function.update (Function.update store
    70 suffix) 1 ((Encoding.array Encoding.natural).encode result.2))
    64 ((Encoding.array Encoding.node).encode result.1))
    72 (List.replicate result.2.size true)) 73 []

theorem stepBudget_source_mono (mapping : Array Nat) (pool : Array Executable.Node)
    (node : Executable.Node) {small large : Nat} (bound : small ≤ large) :
    stepBudget mapping pool node small ≤ stepBudget mapping pool node large := by
  unfold stepBudget
  exact Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.add_le_add_right (Nat.mul_le_mul_left 2100 (Nat.pow_le_pow_left (by omega) 3)) _) _) _

/-- All source nodes are physically read, remapped and interned. The return
value is exactly the fold used by the executable importer, including its
index table; no validity or distinctness premise is needed. -/
theorem loop_executes (store : Store 94) (mapping : Array Nat) (pool : Array Executable.Node)
    (nodes : List Executable.Node) (suffix : List Bool) (L : Nat)
    (source : store 70=Encoding.sequence Encoding.node nodes++suffix)
    (status : store 71=[true])
    (mappingAt : store 1=(Encoding.array Encoding.natural).encode mapping)
    (poolAt : store 64=(Encoding.array Encoding.node).encode pool)
    (counter : store 72=List.replicate mapping.size true)
    (remaining : store 73=List.replicate nodes.length true)
    (zero : store 0=[])
    (empty : ∀ r : Fin 96,2 ≤ r.val → r.val ≤ 68 → r≠64 → store r=[])
    (sourceLimit : (store 70).length ≤ L) :
    ∃ time ≤ loopBudget mapping pool nodes L,
      Executes loop store time (imported store mapping pool nodes suffix) := by
  induction nodes generalizing store mapping pool with
  | nil =>
    have remainingEmpty : store 73=[] := by simpa using remaining
    have sourceAt : store 70=suffix := by simpa [Encoding.sequence] using source
    obtain ⟨ran,halted⟩ := repeat_empty (73:Fin 96) step store remainingEmpty
    have final : imported store mapping pool [] suffix=store := by
      funext r
      by_cases r1 : r=1 <;> by_cases r64 : r=64 <;> by_cases r70 : r=70 <;>
        by_cases r72 : r=72 <;> by_cases r73 : r=73 <;>
        simp [imported,r1,r64,r70,r72,r73,sourceAt,remainingEmpty,counter,mappingAt,poolAt]
    exact ⟨1,by simp [loopBudget],⟨1,store⟩,ran,halted,final.symm⟩
  | cons node nodes ih =>
    let consumed := Function.update store 73 (List.replicate nodes.length true)
    have consumedEmpty (r : Fin 96) (lower : 2 ≤ r.val) (upper : r.val ≤ 68)
        (different : r≠64) : consumed r=[] := by
      have n73 : r≠73 := by intro equal;subst r;norm_num at upper
      simp [consumed,n73,empty r lower upper different]
    obtain ⟨bodyTime,bodyBound,bodyFinish,bodyRun,bodyHalt,bodyStore⟩ := step_executes
      consumed mapping pool node (Encoding.sequence Encoding.node nodes++suffix)
      (by simpa [consumed,Encoding.sequence,List.append_assoc] using source)
      (by simp [consumed,status]) (by simp [consumed,mappingAt]) (by simp [consumed,poolAt])
      (by simp [consumed,counter]) (by simp [consumed,zero]) consumedEmpty
    let next := advance (pool,mapping) node
    let middle := stepped consumed mapping pool node (Encoding.sequence Encoding.node nodes++suffix)
    have middleEmpty (r : Fin 96) (lower : 2 ≤ r.val) (upper : r.val ≤ 68)
        (different : r≠64) : middle r=[] := by
      have n1 : r≠1 := by intro equal;subst r;norm_num at lower
      have n70 : r≠70 := by intro equal;subst r;norm_num at upper
      have n72 : r≠72 := by intro equal;subst r;norm_num at upper
      simp [middle,stepped,n1,n70,n72,different,consumedEmpty r lower upper different]
    have tailSize : (middle 70).length ≤ L := by
      have inputLength : (store 70).length=(Encoding.node.encode node).length+
          (Encoding.sequence Encoding.node nodes++suffix).length := by
        rw [source]
        simp [Encoding.sequence,List.length_append]
      simp only [middle,stepped,Function.update_of_ne (show (70:Fin 96)≠72 by decide),
        Function.update_of_ne (show (70:Fin 96)≠64 by decide),
        Function.update_of_ne (show (70:Fin 96)≠1 by decide),Function.update_self]
      omega
    obtain ⟨tailTime,tailBound,tailFinish,tailRun,tailHalt,tailStore⟩ := ih middle next.2 next.1
      (by simp [middle,stepped]) (by simp [middle,stepped,consumed,status])
      (by simp [middle,stepped,next,advance]) (by simp [middle,stepped,next,advance])
      (by simp [middle,stepped,next,advance]) (by simp [middle,stepped,consumed])
      (by simp [middle,stepped,consumed,zero]) middleEmpty tailSize
    have firstRun := repeat_iteration (73:Fin 96) step store true (List.replicate nodes.length true)
      (by simpa only [List.length_cons,List.replicate_succ] using remaining)
      bodyTime bodyFinish bodyRun bodyHalt
    have final : imported middle next.2 next.1 nodes suffix=
        imported store mapping pool (node::nodes) suffix := by
      funext r
      by_cases r1 : r=1 <;> by_cases r64 : r=64 <;> by_cases r70 : r=70 <;>
        by_cases r72 : r=72 <;> by_cases r73 : r=73 <;>
        simp [imported,List.foldl_cons,middle,stepped,consumed,next,advance,r1,r64,r70,r72,r73]
    refine ⟨bodyTime+2+tailTime,?_,tailFinish,?_,tailHalt,tailStore.trans final⟩
    · have inputSame : consumed 70=store 70 := by simp [consumed]
      rw [inputSame] at bodyBound
      have bounded := bodyBound.trans (stepBudget_source_mono mapping pool node sourceLimit)
      change bodyTime+2+tailTime ≤ stepBudget mapping pool node L+2+loopBudget next.2 next.1 nodes L
      omega
    · rw [Machine.run_add,firstRun,Option.bind_some,bodyStore]
      exact tailRun

end Counting.StackMachine.DagUpdate.Import
