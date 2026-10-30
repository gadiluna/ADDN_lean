import Counting.HardnessNetworkMachineMatrixHead

namespace Counting.HardnessNetworkMachine
open StackMachine StackMachine.Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def MatrixWorkspace.group (w : MatrixWorkspace extra) : GroupWorkspace (extra+4) := w.groups.group

def baselineGroupScratch : List (Fin 16) := [1,3,4,5,6,7,8,9,11]

def emitBaselineGroup (extra : Nat) (w : MatrixWorkspace extra) : Routine (extra+14) :=
  sequence (prepend (w 1) [true,true])
    (sequence (pushBit (w 10) true)
      (sequence (emitGroup (extra+4) w.group) (discardBit (w 10))))

def baselineGroupResult (w : MatrixWorkspace extra) (store : Fin (extra+16) → List Bool) (base : Nat) :=
  Function.update (Function.update store (w 1) (List.replicate (base+3) true)) (w 2)
    ((Encoding.sequence (Encoding.list Encoding.natural) (groupRows (store (w 0)).length 1 (base+1))).reverse++store (w 2))

theorem emitBaselineGroup_executes (extra : Nat) (w : MatrixWorkspace extra)
    (store : Fin (extra+16) → List Bool) (base : Nat)
    (baseValue : store (w 10)=List.replicate base true)
    (inside : base+2 ≤ (store (w 0)).length)
    (empty : ∀ i∈baselineGroupScratch,store (w i)=[]) :
    ∃ time ≤ groupCost (store (w 0)).length (base+1)+9,
      Executes (emitBaselineGroup extra w) store time (baselineGroupResult w store base) := by
  have preparing:=prepend_executes (w 1) [true,true] store
  rw [empty 1 (by simp [baselineGroupScratch]),List.append_nil] at preparing
  let indexed:=Function.update store (w 1) [true,true]
  have enlarging:=pushBit_executes (w 10) true indexed
  have baseAt : indexed (w 10)=List.replicate base true := by simp [indexed,w.injective.eq_iff,baseValue]
  rw [baseAt] at enlarging
  let enlarged:=Function.update indexed (w 10) (List.replicate (base+1) true)
  have enlargeAs : Executes (pushBit (w 10) true) indexed 1 enlarged := by
    simpa only [enlarged,List.replicate_succ] using enlarging
  have groupEmpty (i : Fin 12) (member : i∈groupScratch) : enlarged (w.group i)=[] := by
    simp only [groupScratch,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp [MatrixWorkspace.group,MatrixWorkspace.groups,matrixGroupsPositions,GroupsWorkspace.group,groupsPositions,
      enlarged,indexed,w.injective.eq_iff,empty,baselineGroupScratch]
  obtain ⟨groupTime,groupBound,groupRun⟩:=emitGroup_executes (extra+4) w.group 1 (base+1) enlarged (by omega)
    (by simp [MatrixWorkspace.group,MatrixWorkspace.groups,matrixGroupsPositions,GroupsWorkspace.group,groupsPositions,
      enlarged,indexed,w.injective.eq_iff])
    (by simp [MatrixWorkspace.group,MatrixWorkspace.groups,matrixGroupsPositions,GroupsWorkspace.group,groupsPositions,enlarged])
    (by simpa [MatrixWorkspace.group,MatrixWorkspace.groups,matrixGroupsPositions,GroupsWorkspace.group,groupsPositions,
      enlarged,indexed,w.injective.eq_iff,Nat.add_comm,Nat.add_left_comm] using inside) groupEmpty
  let grouped:=groupResult w.group enlarged 1 (base+1)
  have skipping:=discardBit_executes (w 10) grouped
  have final : Function.update grouped (w 10) (grouped (w 10)).tail=baselineGroupResult w store base := by
    have joined : List.replicate (base+1) true++[true,true]=List.replicate (base+3) true := by
      change List.replicate (base+1) true++List.replicate 2 true=_
      rw [←List.replicate_add]
    funext r
    by_cases e10 : r=w 10
    · subst r;simp [grouped,groupResult,MatrixWorkspace.group,MatrixWorkspace.groups,matrixGroupsPositions,GroupsWorkspace.group,groupsPositions,
        enlarged,indexed,baselineGroupResult,w.injective.eq_iff,List.replicate_succ,baseValue]
    · by_cases e1 : r=w 1
      · subst r;simp [grouped,groupResult,MatrixWorkspace.group,MatrixWorkspace.groups,matrixGroupsPositions,GroupsWorkspace.group,groupsPositions,
          enlarged,indexed,baselineGroupResult,w.injective.eq_iff,joined]
      · by_cases e2 : r=w 2
        · subst r;simp [grouped,groupResult,MatrixWorkspace.group,MatrixWorkspace.groups,matrixGroupsPositions,GroupsWorkspace.group,groupsPositions,
            enlarged,indexed,baselineGroupResult,w.injective.eq_iff]
        · simp [grouped,groupResult,MatrixWorkspace.group,MatrixWorkspace.groups,matrixGroupsPositions,GroupsWorkspace.group,groupsPositions,
            enlarged,indexed,baselineGroupResult,e10,e1,e2]
  rw [final] at skipping
  have combined:=preparing.sequence (enlargeAs.sequence (groupRun.sequence skipping))
  refine ⟨_,?_,combined⟩
  have bound : groupTime ≤ groupCost (store (w 0)).length (base+1) := by
    simpa [MatrixWorkspace.group,MatrixWorkspace.groups,matrixGroupsPositions,GroupsWorkspace.group,groupsPositions,
      enlarged,indexed,w.injective.eq_iff] using groupBound
  change 2*[true,true].length+1+(1+1+(groupTime+1+1)) ≤ _
  simp only [List.length_cons,List.length_nil]
  omega

end Counting.HardnessNetworkMachine
