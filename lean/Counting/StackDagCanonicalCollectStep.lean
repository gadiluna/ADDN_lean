import Counting.StackDagCanonicalCollectLevel
import Counting.StackDagCanonicalCollectSelect

namespace Counting.StackMachine.DagUpdate.Canonical
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-- The collector workspace excludes the immutable mapping and canonical pool. -/
def CollectScratch (store : Store 94) : Prop :=
  ∀ r : Fin 96, 2 ≤ r.val → r.val ≤ 79 → r ≠ 64 → store r=[]

def collectStep : Routine 94 := sequence Import.mapNode
  (sequence collectLevel (sequence chooseRecord (pushBit 83 true)))

def collectStepResult (store : Store 94) (mapping : Array Nat) (node : Executable.Node)
    (suffix : List Bool) (index level : Nat) : Store 94 :=
  let base := Function.update (Function.update store 0 suffix) 83 (List.replicate (index+1) true)
  if node.level=level then
    Function.update (Function.update base 85
      (Sort.recordCodec.encode (index,Executable.referenceMap mapping node)++store 85)) 86 (true::store 86)
  else base

def collectStepBudget (store : Store 94) (mapping : Array Nat) (node : Executable.Node)
    (index level : Nat) : Nat :=
  30000000000*((store 0).length+(store 1).length+1)^7+
  30*((Encoding.node.encode (Executable.referenceMap mapping node)).length+level.bits.length+1)+
  101*(index+(Encoding.node.encode (Executable.referenceMap mapping node)).length+1)^2+4

theorem collectStep_executes (store : Store 94) (mapping : Array Nat) (node : Executable.Node)
    (suffix : List Bool) (index level : Nat)
    (source : store 0=Encoding.node.encode node++suffix)
    (mappingAt : store 1=(Encoding.array Encoding.natural).encode mapping)
    (indexAt : store 83=List.replicate index true) (levelAt : store 82=level.bits)
    (empty : CollectScratch store) :
    ∃ time ≤ collectStepBudget store mapping node index level,
      Executes collectStep store time (collectStepResult store mapping node suffix index level) := by
  let target := Executable.referenceMap mapping node
  let a := Function.update (Function.update store 0 suffix) 3 (Encoding.node.encode target)
  obtain ⟨t0,b0,r0⟩ := Import.mapNode_executes store mapping node suffix source mappingAt
    (fun r lower upper=>empty r lower (by omega) (by intro eq;subst r;omega))
  obtain ⟨t1,b1,r1⟩ := collectLevel_executes a target level (by simp [a])
    (by simp [a,levelAt]) (by
      intro r eligible
      have lo : 2 ≤ r.val := by rcases eligible with rfl|bounds <;> simp_all; omega
      have hi : r.val ≤ 79 := by rcases eligible with rfl|bounds <;> simp_all;omega
      have n0 : r ≠ 0 := by intro eq;subst r;omega
      have n3 : r ≠ 3 := by rcases eligible with rfl|bounds <;> simp_all;intro eq;subst r;omega
      have n64 : r ≠ 64 := by rcases eligible with rfl|bounds <;> simp_all;intro eq;subst r;omega
      simp [a,n0,n3,empty r lo hi n64])
  let b := Function.update a 67 [decide (target.level=level)]
  obtain ⟨t2,b2,r2⟩ := chooseRecord_executes b index target (decide (target.level=level))
    (by simp [b,a]) (by simp [b,a,indexAt]) (by simp [b])
    (by simp [b,a,empty 2 (by decide) (by decide) (by decide)])
    (by simp [b,a,empty 4 (by decide) (by decide) (by decide)])
    (by simp [b,a,empty 5 (by decide) (by decide) (by decide)])
  let c := chosenRecordStore b index target (decide (target.level=level))
  have push := pushBit_executes (83:Fin 96) true c
  have final : Function.update c 83 (true::c 83)=collectStepResult store mapping node suffix index level := by
    have e3 := empty 3 (by decide) (by decide) (by decide)
    have e67 := empty 67 (by decide) (by decide) (by decide)
    have targetLevel : target.level=node.level := rfl
    funext r
    by_cases selected : node.level=level
    · by_cases r0 : r=0 <;> by_cases r3 : r=3 <;> by_cases r67 : r=67 <;>
        by_cases r83 : r=83 <;> by_cases r85 : r=85 <;> by_cases r86 : r=86 <;>
        simp [c,chosenRecordStore,selectedRecordStore,b,a,collectStepResult,
          targetLevel,selected,r0,r3,r67,r83,r85,r86,e3,e67,indexAt,List.replicate_succ,target]
    · by_cases r0 : r=0 <;> by_cases r3 : r=3 <;> by_cases r67 : r=67 <;>
        by_cases r83 : r=83 <;>
        simp [c,chosenRecordStore,b,a,collectStepResult,
          targetLevel,selected,r0,r3,r67,r83,e3,e67,indexAt,List.replicate_succ]
  rw [final] at push
  refine ⟨_,?_,r0.sequence (r1.sequence (r2.sequence push))⟩
  dsimp only [collectStepBudget]
  have a3 : a 3=Encoding.node.encode target := by simp [a]
  have a82 : a 82=level.bits := by simp [a,levelAt]
  rw [a3,a82] at b1
  dsimp only [target] at b1 b2
  omega

end Counting.StackMachine.DagUpdate.Canonical
