import Counting.StackAnchorNodeFields
import Counting.StackAnchorFind
import Counting.StackAnchorDifference
import Counting.StackDagIncrement

namespace Counting.StackMachine.AnchorCoefficient
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

/-- Private lookup cells0–20 are disjoint from the persistent arithmetic
and node fields. Only cell0 remains live as the unread input suffix. -/
def file (input query result level parent leader degree count successor flag : List Bool) : Store 32 :=
  fun r=>if r=0 then input else if r=21 then query else if r=22 then result
    else if r=23 then level else if r=24 then parent else if r=25 then leader
    else if r=26 then degree else if r=27 then count else if r=28 then successor
    else if r=32 then flag else []

def nodeRoles : Fin 9 ↪ Fin 34 := ⟨![0,23,24,25,26,1,2,3,4],by decide⟩
def findRoles : Fin 21 ↪ Fin 34 := ⟨![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,21,27,19,20],by decide⟩
def differenceRoles : Fin 16 ↪ Fin 34 := ⟨![1,2,3,4,5,6,7,8,9,10,11,12,27,26,30,22],by decide⟩
def equalityRoles : Fin 6 ↪ Fin 34 := ⟨![24,28,32,1,2,3],by decide⟩
abbrev readNode : Routine 32 := relocate AnchorNode.fields nodeRoles
abbrev findCount : Routine 32 := relocate AnchorFind.lookup findRoles
abbrev subtract : Routine 32 := relocate AnchorDifference.difference differenceRoles
abbrev prepareQuery : Routine 32 := sequence (ofProgram (ListPrograms.copyProgram 31 21 28 30))
  (DagValidation.incrementRoutine 31 31 28 30)

theorem readNode_executes (node : Executable.Node) (query : Nat) (suffix result : List Bool) :
    ∃ time  ≤  10*(Encoding.node.encode node++suffix).length+30,
      Executes readNode (file (Encoding.node.encode node++suffix) query.bits result [] [] [] [] [] [] []) time
        (file ((Encoding.list AnchorFind.edgeCodec).encode node.incoming++suffix) query.bits result
          node.level.bits (DagValidation.parentCode node).bits [node.leader] node.degree.bits [] [] []) := by
  obtain ⟨time,bounded,ran⟩ := AnchorNode.fields_executes node suffix
  refine ⟨time,bounded,?_⟩
  apply relocate_executes_frame AnchorNode.fields nodeRoles _ _ _ _ time _ _ _ ran
  · funext r;fin_cases r <;> simp [file,AnchorNode.file,nodeRoles]
  · intro r;fin_cases r <;> simp [file,AnchorNode.file,nodeRoles,AnchorFind.edgeCodec]
  · intro r outside
    have n0 : r≠0 := by intro eq;subst r;exact outside 0 rfl
    have n23 : r≠23 := by intro eq;subst r;exact outside 1 rfl
    have n24 : r≠24 := by intro eq;subst r;exact outside 2 rfl
    have n25 : r≠25 := by intro eq;subst r;exact outside 3 rfl
    have n26 : r≠26 := by intro eq;subst r;exact outside 4 rfl
    simp [file,n0,n23,n24,n25,n26]

theorem findCount_executes (node : Executable.Node) (query : Nat) (suffix result : List Bool) :
    ∃ time  ≤  5000*(((Encoding.list AnchorFind.edgeCodec).encode node.incoming++suffix).length+query.size+1)^3,
      Executes findCount
        (file ((Encoding.list AnchorFind.edgeCodec).encode node.incoming++suffix) query.bits result
          node.level.bits (DagValidation.parentCode node).bits [node.leader] node.degree.bits [] [] []) time
        (file suffix query.bits result node.level.bits (DagValidation.parentCode node).bits [node.leader]
          node.degree.bits (Executable.countFrom node query).bits [] []) := by
  obtain ⟨time,bounded,ran⟩ := AnchorFind.lookup_countFrom node query suffix
  refine ⟨time,bounded,?_⟩
  apply relocate_executes_frame AnchorFind.lookup findRoles _ _ _ _ time _ _ _ ran
  · funext r;fin_cases r <;> simp [file,AnchorFind.bank,findRoles]
  · intro r;fin_cases r <;> simp [file,AnchorFind.bank,findRoles]
  · intro r outside
    have n0 : r≠0 := by intro eq;subst r;exact outside 0 rfl
    have n27 : r≠27 := by intro eq;subst r;exact outside 18 rfl
    simp [file,n0,n27]

theorem prepareQuery_executes (store : Store 32) (query : Nat) (encoded : store 21=query.bits)
    (empty : store 28=[]) (scratch : store 30=[]) (counter : store 31=[]) :
    ∃ time  ≤  9*query.size+10,
      Executes prepareQuery store time (Function.update store 28 (query+1).bits) := by
  have copied := copy_executes 31 (21:Fin 34) 28 30 (by decide) (by decide) (by decide) store scratch
  rw [encoded,empty,List.append_nil] at copied
  let ready := Function.update store 28 query.bits
  obtain ⟨time,bounded,ran⟩ := DagValidation.increment_natural 31 (31:Fin 34) 28 30
    (by decide) (by decide) (by decide) ready (by simp [ready,counter]) (by simp [ready,scratch]) query (by simp [ready])
  have final : Function.update ready 28 (query+1).bits=Function.update store 28 (query+1).bits := by
    simp only [ready,Function.update_idem]
  rw [final] at ran
  refine ⟨5*query.bits.length+2+1+time,?_,copied.sequence ran⟩
  rw [Encoding.bits_length]
  omega

end Counting.StackMachine.AnchorCoefficient
