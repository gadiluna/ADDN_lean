import Counting.StackDagCanonicalCollectStep

namespace Counting.StackMachine.DagUpdate.Canonical
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

private theorem sequence_append (first last : List Sort.Record) :
    Encoding.sequence Sort.recordCodec (first++last)=
      Encoding.sequence Sort.recordCodec first++Encoding.sequence Sort.recordCodec last := by
  induction first with
  | nil => rfl
  | cons value rest ih => simp [Encoding.sequence,ih,List.append_assoc]

private theorem replicate_cons_append (n : Nat) (suffix : List Bool) :
    List.replicate n true++true::suffix=true::(List.replicate n true++suffix) := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [List.replicate_succ,List.cons_append] using congrArg (true::·) ih

/-- Original node indices remain attached to remapped signatures. -/
def collectEntries (mapping : Array Nat) (level : Nat) : Nat → List Executable.Node → List Sort.Record
  | _,[] => []
  | index,node::nodes =>
      let tail := collectEntries mapping level (index+1) nodes
      if node.level=level then (index,Executable.referenceMap mapping node)::tail else tail

abbrev collectLoop : Routine 94 := forEach 84 collectStep

def collectLoopBudget (mapping : Array Nat) (level : Nat) : Nat → List Executable.Node → List Bool → Nat
  | _,[],_ => 1
  | index,node::nodes,suffix =>
      30000000000*((Encoding.sequence Encoding.node (node::nodes)++suffix).length+
        ((Encoding.array Encoding.natural).encode mapping).length+1)^7+
      30*((Encoding.node.encode (Executable.referenceMap mapping node)).length+level.bits.length+1)+
      101*(index+(Encoding.node.encode (Executable.referenceMap mapping node)).length+1)^2+6+
      collectLoopBudget mapping level (index+1) nodes suffix

def collectLoopResult (store : Store 94) (mapping : Array Nat) (nodes : List Executable.Node)
    (suffix : List Bool) (index level : Nat) : Store 94 :=
  let entries := collectEntries mapping level index nodes
  Function.update (Function.update (Function.update (Function.update (Function.update store
    0 suffix) 83 (List.replicate (index+nodes.length) true)) 84 [])
    85 (Encoding.sequence Sort.recordCodec entries.reverse++store 85))
    86 (List.replicate entries.length true++store 86)

theorem collectStepResult_scratch (store : Store 94) (mapping : Array Nat)
    (node : Executable.Node) (suffix : List Bool) (index level : Nat) (empty : CollectScratch store) :
    CollectScratch (collectStepResult store mapping node suffix index level) := by
  intro r lo hi n64
  have n0 : r≠0 := by intro eq;subst r;omega
  have n83 : r≠83 := by intro eq;subst r;omega
  have n85 : r≠85 := by intro eq;subst r;omega
  have n86 : r≠86 := by intro eq;subst r;omega
  simp [collectStepResult,ite_apply,n0,n83,n85,n86,empty r lo hi n64]

theorem collectLoop_executes (store : Store 94) (mapping : Array Nat) (nodes : List Executable.Node)
    (suffix : List Bool) (index level : Nat)
    (source : store 0=Encoding.sequence Encoding.node nodes++suffix)
    (mappingAt : store 1=(Encoding.array Encoding.natural).encode mapping)
    (indexAt : store 83=List.replicate index true) (levelAt : store 82=level.bits)
    (counter : store 84=List.replicate nodes.length true) (empty : CollectScratch store) :
    ∃ time ≤ collectLoopBudget mapping level index nodes suffix,
      Executes collectLoop store time (collectLoopResult store mapping nodes suffix index level) := by
  induction nodes generalizing store index with
  | nil =>
    have counterEmpty : store 84=[] := by simpa using counter
    obtain ⟨run,halt⟩ := repeat_empty (84:Fin 96) collectStep store counterEmpty
    have final : collectLoopResult store mapping [] suffix index level=store := by
      funext r
      by_cases r0 : r=0 <;> by_cases r83 : r=83 <;> by_cases r84 : r=84 <;>
        by_cases r85 : r=85 <;> by_cases r86 : r=86 <;>
        simp_all [collectLoopResult,collectEntries,Encoding.sequence]
    exact ⟨1,le_rfl,⟨1,store⟩,run,halt,final.symm⟩
  | cons node nodes ih =>
    let consumed := Function.update store 84 (List.replicate nodes.length true)
    have scratch : CollectScratch consumed := by
      intro r lo hi n64
      have n84 : r≠84 := by intro eq;subst r;omega
      simp [consumed,n84,empty r lo hi n64]
    obtain ⟨tb,bb,bodyFinish,bodyRun,bodyHalt,bodyStore⟩ := collectStep_executes consumed mapping node
      (Encoding.sequence Encoding.node nodes++suffix) index level
      (by simpa [consumed,Encoding.sequence,List.append_assoc] using source)
      (by simp [consumed,mappingAt]) (by simp [consumed,indexAt]) (by simp [consumed,levelAt]) scratch
    let middle := collectStepResult consumed mapping node (Encoding.sequence Encoding.node nodes++suffix) index level
    obtain ⟨tt,bt,tailFinish,tailRun,tailHalt,tailStore⟩ := ih middle (index+1)
      (by simp [middle,collectStepResult,ite_apply]) (by simp [middle,collectStepResult,ite_apply,consumed,mappingAt])
      (by simp [middle,collectStepResult,ite_apply]) (by simp [middle,collectStepResult,ite_apply,consumed,levelAt])
      (by simp [middle,collectStepResult,ite_apply,consumed])
      (collectStepResult_scratch consumed mapping node _ index level scratch)
    have iteration := repeat_iteration (84:Fin 96) collectStep store true
      (List.replicate nodes.length true)
      (by simpa only [List.length_cons,List.replicate_succ] using counter)
      tb bodyFinish bodyRun bodyHalt
    have final : collectLoopResult middle mapping nodes suffix (index+1) level=
        collectLoopResult store mapping (node::nodes) suffix index level := by
      funext r
      by_cases selected : node.level=level <;>
        by_cases r0 : r=0 <;> by_cases r83 : r=83 <;> by_cases r84 : r=84 <;>
        by_cases r85 : r=85 <;> by_cases r86 : r=86 <;>
        simp [collectLoopResult,collectEntries,middle,collectStepResult,consumed,selected,
          r0,r83,r84,r85,r86,List.reverse_cons,sequence_append,Encoding.sequence,
          List.append_assoc,replicate_cons_append,List.replicate_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
      all_goals rw [Nat.add_comm 1]; rfl
    refine ⟨tb+2+tt,?_,tailFinish,?_,tailHalt,tailStore.trans final⟩
    · have sourceAt : consumed 0=Encoding.sequence Encoding.node (node::nodes)++suffix := by
        simpa [consumed] using source
      have mapAt : consumed 1=(Encoding.array Encoding.natural).encode mapping := by simp [consumed,mappingAt]
      dsimp only [collectStepBudget] at bb
      rw [sourceAt,mapAt] at bb
      dsimp only [collectLoopBudget]
      omega
    · rw [Machine.run_add,iteration,Option.bind_some,bodyStore]
      exact tailRun

end Counting.StackMachine.DagUpdate.Canonical
