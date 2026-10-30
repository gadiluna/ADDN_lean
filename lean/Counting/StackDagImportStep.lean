import Counting.StackDagImportRead
import Counting.StackDagMapIntern
import Counting.StackDagImportCommit

namespace Counting.StackMachine.DagUpdate.Import
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000

def step : Routine 94 := sequence readImportNode (sequence mapIntern commitNode)

def stepBudget (mapping : Array Nat) (pool : Array Executable.Node) (node : Executable.Node)
    (sourceLength : Nat) : Nat :=
  let result := Executable.intern pool (Executable.referenceMap mapping node)
  2100*(sourceLength+1)^3+mapInternBudget mapping pool node []+
    commitBudget mapping pool result.1 result.2+2

def stepped (store : Store 94) (mapping : Array Nat) (pool : Array Executable.Node)
    (node : Executable.Node) (suffix : List Bool) : Store 94 :=
  let result := Executable.intern pool (Executable.referenceMap mapping node)
  Function.update (Function.update (Function.update (Function.update store 70 suffix)
    1 ((Encoding.array Encoding.natural).encode (mapping.push result.2)))
    64 ((Encoding.array Encoding.node).encode result.1)) 72 (List.replicate (mapping.size+1) true)

/-- One literal iteration of the executable import fold. The source node
is parsed, remapped, interned, and its returned index appended physically. -/
theorem step_executes (store : Store 94) (mapping : Array Nat) (pool : Array Executable.Node)
    (node : Executable.Node) (suffix : List Bool)
    (source : store 70=Encoding.node.encode node++suffix) (status : store 71=[true])
    (mappingAt : store 1=(Encoding.array Encoding.natural).encode mapping)
    (poolAt : store 64=(Encoding.array Encoding.node).encode pool)
    (counter : store 72=List.replicate mapping.size true) (zero : store 0=[])
    (empty : ∀ r : Fin 96,2 ≤ r.val → r.val ≤ 68 → r≠64 → store r=[]) :
    ∃ time ≤ stepBudget mapping pool node (store 70).length,
      Executes step store time (stepped store mapping pool node suffix) := by
  obtain ⟨readTime,readBound,readRun⟩ := readImportNode_executes store node suffix source status zero
    (fun r lower upper=>empty r lower (by omega) (by intro eq;subst r;norm_num at upper))
  let read := Function.update (Function.update store 70 suffix) 0 (Encoding.node.encode node)
  have readEmpty (r : Fin 96) (lower : 2 ≤ r.val) (upper : r.val ≤ 68) (different : r≠64) : read r=[] := by
    have n0 : r≠0 := by intro eq;subst r;norm_num at lower
    have n70 : r≠70 := by intro eq;subst r;norm_num at upper
    simp [read,n0,n70,empty r lower upper different]
  obtain ⟨mapTime,mapBound,mapRun⟩ := mapIntern_executes read mapping pool node []
    (by simp [read]) (by simp [read,mappingAt]) (by simp [read,poolAt]) readEmpty
  let result := Executable.intern pool (Executable.referenceMap mapping node)
  let mapped := Function.update (Function.update (Function.update read 0 []) 65
    ((Encoding.array Encoding.node).encode result.1)) 66 result.2.bits
  obtain ⟨commitTime,commitBound,commitRun⟩ := commitNode_executes mapped mapping pool result.1 result.2
    (by simp [mapped,read,mappingAt]) (by simp [mapped,read,poolAt])
    (by simp [mapped]) (by simp [mapped]) (by simp [mapped,read,counter]) (by
      intro r lower upper
      have n0 : r≠0 := by intro eq;subst r;norm_num at lower
      have n65 : r≠65 := by intro eq;subst r;norm_num at upper
      have n66 : r≠66 := by intro eq;subst r;norm_num at upper
      simp [mapped,n0,n65,n66,readEmpty r lower (by omega) (by intro eq;subst r;norm_num at upper)])
  have final : committed mapped mapping result.1 result.2=stepped store mapping pool node suffix := by
    funext r
    fin_cases r <;> simp [committed,mapped,read,stepped,result,zero,empty]
  rw [final] at commitRun
  refine ⟨_,?_,readRun.sequence (mapRun.sequence commitRun)⟩
  dsimp only [stepBudget]
  dsimp only [result] at commitBound
  omega

end Counting.StackMachine.DagUpdate.Import
