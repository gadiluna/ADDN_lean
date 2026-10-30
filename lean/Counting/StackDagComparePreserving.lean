import Counting.StackDagCompare
import Counting.StackRoutineLists

namespace Counting.StackMachine.DagUpdate.Key
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000

def wideComparisonRoles : Fin 64 ↪ Fin 72 :=
  ⟨fun r=>⟨r.val,by omega⟩,by intro a b equal;exact Fin.ext (congrArg (fun r : Fin 72=>r.val) equal)⟩

def compareWide : Routine 70 := relocate compareNodes wideComparisonRoles

private theorem compareWide_executes (store : Store 70) (left right : Executable.Node)
    (leftAt : store 0=Encoding.node.encode left) (rightAt : store 1=Encoding.node.encode right)
    (empty : ∀ r : Fin 72,(2≤r.val ∧ r.val≤13) ∨ (40≤r.val ∧ r.val≤44) ∨
      (49≤r.val ∧ r.val≤51) → store r=[]) :
    ∃ time≤10000*((store 0).length+(store 1).length+1)^2,
      Executes compareWide store time
        (Function.update (Function.update (Function.update store 0 []) 1 [])
          2 [Executable.lexLE left.key right.key]) := by
  let localStore : Store 62 := store ∘ wideComparisonRoles
  obtain ⟨time,bounded,run⟩ := compareNodes_executes localStore left right leftAt rightAt (by
    intro r allowed
    exact empty (wideComparisonRoles r) allowed)
  refine ⟨time,bounded,?_⟩
  apply relocate_executes_frame compareNodes wideComparisonRoles store _ localStore
    (nodesComparisonResult localStore left right) time rfl _ _ run
  · intro r
    fin_cases r <;> simp [wideComparisonRoles,nodesComparisonResult,localStore]
  · intro r outside
    have n0 : r≠0 := fun same=>outside 0 (by simpa [wideComparisonRoles] using same.symm)
    have n1 : r≠1 := fun same=>outside 1 (by simpa [wideComparisonRoles] using same.symm)
    have n2 : r≠2 := fun same=>outside 2 (by simpa [wideComparisonRoles] using same.symm)
    simp [n0,n1,n2]

def preservingNodes : Routine 70 := sequence (ofProgram (ListPrograms.copyProgram 69 64 0 67))
  (sequence (ofProgram (ListPrograms.copyProgram 69 65 1 67))
    (sequence compareWide (move 69 2 66 67)))

/-- The sorting loop may retain both complete serialized records while
comparing their node signatures. Both copies and all cleanup are charged. -/
theorem preservingNodes_executes (store : Store 70) (left right : Executable.Node)
    (leftAt : store 64=Encoding.node.encode left) (rightAt : store 65=Encoding.node.encode right)
    (empty : ∀ r : Fin 72,r.val≤13 ∨ (40≤r.val ∧ r.val≤44) ∨
      (49≤r.val ∧ r.val≤51) ∨ r=67 → store r=[]) :
    ∃ time≤11000*((store 64).length+(store 65).length+1)^2,
      Executes preservingNodes store time
        (Function.update store 66 (Executable.lexLE left.key right.key::store 66)) := by
  have first := copy_executes 69 (64:Fin 72) 0 67 (by decide) (by decide) (by decide)
    store (empty 67 (by simp))
  rw [empty 0 (by simp),List.append_nil] at first
  let s1 := Function.update store 0 (store 64)
  have second := copy_executes 69 (65:Fin 72) 1 67 (by decide) (by decide) (by decide)
    s1 (by simp [s1,empty])
  have source : s1 65=store 65 := by simp [s1]
  have target : s1 1=[] := by simp [s1,empty]
  rw [source,target,List.append_nil] at second
  let s2 := Function.update s1 1 (store 65)
  obtain ⟨time,bounded,compared⟩ := compareWide_executes s2 left right
    (by simp [s2,s1,leftAt]) (by simp [s2,rightAt]) (by
      intro r allowed
      fin_cases r <;> simp_all [s2,s1])
  let s3 := Function.update (Function.update (Function.update s2 0 []) 1 [])
    2 [Executable.lexLE left.key right.key]
  have moving := move_executes 69 (2:Fin 72) 66 67 (by decide) (by decide) (by decide)
    s3 (by simp [s3,s2,s1,empty])
  have flag : s3 2=[Executable.lexLE left.key right.key] := by simp [s3]
  have tail : s3 66=store 66 := by simp [s3,s2,s1]
  rw [flag,tail,List.length_singleton,List.singleton_append] at moving
  have final : Function.update (Function.update s3 66 (Executable.lexLE left.key right.key::store 66)) 2 []=
      Function.update store 66 (Executable.lexLE left.key right.key::store 66) := by
    funext r
    fin_cases r <;> simp [s3,s2,s1,empty]
  rw [final] at moving
  refine ⟨_,?_,first.sequence (second.sequence (compared.sequence moving))⟩
  simp only [s2,s1,Function.update_self,Function.update_of_ne (show (0:Fin 72)≠1 by decide)] at bounded
  nlinarith

end Counting.StackMachine.DagUpdate.Key
