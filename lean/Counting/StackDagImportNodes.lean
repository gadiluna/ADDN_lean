import Counting.StackDagImportLoop
import Counting.StackDagImportHeader

namespace Counting.StackMachine.DagUpdate.Import
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def importNodes : Routine 94 := sequence (pushBit 1 false)
  (sequence readHeader (sequence loop (clear 72)))

def importNodesBudget (pool : Array Executable.Node) (nodes : List Executable.Node)
    (sourceLength : Nat) : Nat :=
  1820*(sourceLength+1)^3+loopBudget #[] pool nodes sourceLength+nodes.length+5

theorem fold_mapping_size (nodes : List Executable.Node) (state : Array Executable.Node × Array Nat) :
    (nodes.foldl advance state).2.size=state.2.size+nodes.length := by
  induction nodes generalizing state with
  | nil => simp
  | cons node nodes ih =>
    simp only [List.foldl_cons,ih,advance,Array.size_push,List.length_cons]
    omega

def importResult (store : Store 94) (pool : Array Executable.Node) (nodes : List Executable.Node)
    (suffix : List Bool) : Store 94 :=
  let result := nodes.foldl advance (pool,#[])
  Function.update (Function.update (Function.update store 70 suffix)
    1 ((Encoding.array Encoding.natural).encode result.2))
    64 ((Encoding.array Encoding.node).encode result.1)

/-- Complete physical import of an encoded node list into a supplied pool.
The map begins empty; the header, all iterations, and scratch cleanup are
charged. Only the source, mapping output and pool change. -/
theorem importNodes_executes (store : Store 94) (pool : Array Executable.Node)
    (nodes : List Executable.Node) (suffix : List Bool)
    (source : store 70=(Encoding.list Encoding.node).encode nodes++suffix)
    (poolAt : store 64=(Encoding.array Encoding.node).encode pool)
    (status : store 71=[true])
    (empty : ∀ r : Fin 96,(r.val ≤ 68 ∧ r≠64) ∨ r=72 ∨ r=73 → store r=[]) :
    ∃ time ≤ importNodesBudget pool nodes (store 70).length,
      Executes importNodes store time (importResult store pool nodes suffix) := by
  have initRun := pushBit_executes (1:Fin 96) false store
  rw [empty 1 (by left;decide)] at initRun
  let mapped := Function.update store 1 [false]
  have mappedEmpty (r : Fin 96) (member : (2 ≤ r.val ∧ r.val ≤ 16) ∨ r=73) : mapped r=[] := by
    have n1 : r≠1 := by intro equal;subst r;norm_num [Fin.ext_iff] at member
    have original : store r=[] := empty r (by
      rcases member with first|last
      · left
        constructor
        · omega
        · intro eq
          subst r
          norm_num at first
      · exact Or.inr (Or.inr last))
    simp [mapped,n1,original]
  obtain ⟨headerTime,headerBound,headerRun⟩ := readHeader_executes mapped nodes suffix
    (by simp [mapped,source]) (by simp [mapped,status]) mappedEmpty
  let ready := Function.update (Function.update mapped 70 (Encoding.sequence Encoding.node nodes++suffix))
    73 (List.replicate nodes.length true)
  have readyEmpty (r : Fin 96) (lower : 2 ≤ r.val) (upper : r.val ≤ 68) (different : r≠64) : ready r=[] := by
    have n1 : r≠1 := by intro equal;subst r;norm_num at lower
    have n70 : r≠70 := by intro equal;subst r;norm_num at upper
    have n73 : r≠73 := by intro equal;subst r;norm_num at upper
    simp [ready,mapped,n1,n70,n73,empty r (Or.inl ⟨upper,different⟩)]
  have sourceBound : (ready 70).length ≤ (store 70).length := by
    simp only [ready,Function.update_of_ne (show (70:Fin 96)≠73 by decide),Function.update_self]
    rw [source]
    simp only [Encoding.list,List.length_append]
    omega
  obtain ⟨loopTime,loopBound,loopRun⟩ := loop_executes ready #[] pool nodes suffix (store 70).length
    (by simp [ready]) (by simp [ready,mapped,status]) (by rfl)
    (by simp [ready,mapped,poolAt]) (by simp [ready,mapped,empty]) (by simp [ready])
    (by simp [ready,mapped,empty]) readyEmpty sourceBound
  let result := nodes.foldl advance (pool,#[])
  let after := imported ready #[] pool nodes suffix
  have mapSize : result.2.size=nodes.length := by
    simpa only [Array.size_empty,Nat.zero_add] using fold_mapping_size nodes (pool,#[])
  have cleanup := clear_executes (72:Fin 96) after
  have counter : after 72=List.replicate nodes.length true := by
    simp [after,imported,←mapSize,result]
  rw [counter,List.length_replicate] at cleanup
  have final : Function.update after 72 []=importResult store pool nodes suffix := by
    funext r
    by_cases r1 : r=1 <;> by_cases r64 : r=64 <;> by_cases r70 : r=70 <;>
      by_cases r72 : r=72 <;> by_cases r73 : r=73 <;>
      simp [after,imported,ready,mapped,importResult,r1,r64,r70,r72,r73,empty]
  rw [final] at cleanup
  refine ⟨_,?_,initRun.sequence (headerRun.sequence (loopRun.sequence cleanup))⟩
  have sourceSame : mapped 70=store 70 := by simp [mapped]
  rw [sourceSame] at headerBound
  unfold importNodesBudget
  omega

theorem fold_importVista (pool : Array Executable.Node) (vista : Executable.Vista) :
    vista.nodes.toList.foldl advance (pool,#[])=Executable.importVista pool vista := by
  simp only [Executable.importVista,←Array.foldl_toList]
  rfl

/-- The public specification is the existing executable importer, not a
second importer defined only for the proof. -/
theorem importNodes_executes_importVista (store : Store 94) (pool : Array Executable.Node)
    (vista : Executable.Vista) (suffix : List Bool)
    (source : store 70=(Encoding.array Encoding.node).encode vista.nodes++suffix)
    (poolAt : store 64=(Encoding.array Encoding.node).encode pool)
    (status : store 71=[true])
    (empty : ∀ r : Fin 96,(r.val ≤ 68 ∧ r≠64) ∨ r=72 ∨ r=73 → store r=[]) :
    ∃ time ≤ importNodesBudget pool vista.nodes.toList (store 70).length,
      Executes importNodes store time
        (Function.update (Function.update (Function.update store 70 suffix)
          1 ((Encoding.array Encoding.natural).encode (Executable.importVista pool vista).2))
          64 ((Encoding.array Encoding.node).encode (Executable.importVista pool vista).1)) := by
  obtain ⟨time,bound,ran⟩ := importNodes_executes store pool vista.nodes.toList suffix source poolAt status empty
  exact ⟨time,bound,by simpa only [importResult,fold_importVista] using ran⟩

end Counting.StackMachine.DagUpdate.Import
