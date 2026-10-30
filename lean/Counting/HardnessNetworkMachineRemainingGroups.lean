import Counting.HardnessNetworkMachineMatrixHead

namespace Counting.HardnessNetworkMachine
open StackMachine StackMachine.Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

def remainingGroupsScratch : List (Fin 16) := [3,4,5,6,7,8,9,11,12]

def emitRemainingGroups (extra : Nat) (w : MatrixWorkspace extra) : Routine (extra+14) :=
  sequence (ofProgram (ListPrograms.copyProgram (extra+13) (w 15) (w 12) (w 4)))
    (sequence (emitGroups (extra+3) w.groups) (clear (w 1)))

theorem emitRemainingGroups_executes (extra : Nat) (w : MatrixWorkspace extra)
    (store : Fin (extra+16) → List Bool) (start base count : Nat) (positive : 0<base)
    (index : (store (w 1)).length=start+1)
    (baseValue : store (w 10)=List.replicate base true)
    (countValue : store (w 15)=List.replicate count true)
    (inside : start+count*base ≤ (store (w 0)).length)
    (empty : ∀ i∈remainingGroupsScratch,store (w i)=[]) :
    ∃ time ≤ count*(groupCost (store (w 0)).length base+7)+(store (w 0)).length+10,
      Executes (emitRemainingGroups extra w) store time
        (Function.update (Function.update store (w 1) []) (w 2)
          ((Encoding.sequence (Encoding.list Encoding.natural)
            (ordinaryGroupRows (store (w 0)).length start base count)).reverse++store (w 2))) := by
  have copying:=copy_executes (extra+13) (w 15) (w 12) (w 4)
    (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) store
    (empty 4 (by simp [remainingGroupsScratch]))
  rw [countValue,empty 12 (by simp [remainingGroupsScratch]),List.append_nil,List.length_replicate] at copying
  let ready:=Function.update store (w 12) (List.replicate count true)
  have groupEmpty (i : Fin 12) (member : i∈groupScratch) : ready (w.groups.group i)=[] := by
    simp only [groupScratch,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp [MatrixWorkspace.groups,matrixGroupsPositions,GroupsWorkspace.group,groupsPositions,
      ready,w.injective.eq_iff,empty,remainingGroupsScratch]
  obtain ⟨groupTime,groupBound,groupRun⟩:=emitGroups_executes (extra+3) w.groups start base count ready positive
    (by simpa [MatrixWorkspace.groups,matrixGroupsPositions,ready,w.injective.eq_iff] using index)
    (by simpa [MatrixWorkspace.groups,matrixGroupsPositions,ready,w.injective.eq_iff] using baseValue)
    (by simp [MatrixWorkspace.groups,matrixGroupsPositions,ready])
    (by simpa [MatrixWorkspace.groups,matrixGroupsPositions,ready,w.injective.eq_iff] using inside) groupEmpty
  let grouped:=groupsResult w.groups ready start base count
  have clearing:=clear_executes (w 1) grouped
  have indexLength : (grouped (w 1)).length=count*base+(start+1) := by
    simp [grouped,groupsResult,MatrixWorkspace.groups,matrixGroupsPositions,ready,w.injective.eq_iff,index]
  rw [indexLength] at clearing
  have final : Function.update grouped (w 1) []=
      Function.update (Function.update store (w 1) []) (w 2)
        ((Encoding.sequence (Encoding.list Encoding.natural)
          (ordinaryGroupRows (store (w 0)).length start base count)).reverse++store (w 2)) := by
    funext r
    by_cases e1 : r=w 1
    · subst r;simp [w.injective.eq_iff]
    · by_cases e2 : r=w 2
      · subst r;simp [grouped,groupsResult,MatrixWorkspace.groups,matrixGroupsPositions,ready,w.injective.eq_iff]
      · by_cases e12 : r=w 12
        · subst r;simp [grouped,groupsResult,MatrixWorkspace.groups,matrixGroupsPositions,w.injective.eq_iff,empty,remainingGroupsScratch]
        · simp [grouped,groupsResult,MatrixWorkspace.groups,matrixGroupsPositions,ready,e1,e2,e12]
  rw [final] at clearing
  have combined:=copying.sequence (groupRun.sequence clearing)
  refine ⟨_,?_,combined⟩
  have bounded : groupTime ≤ count*(groupCost (store (w 0)).length base+2)+1 := by
    simpa [MatrixWorkspace.groups,matrixGroupsPositions,ready,w.injective.eq_iff] using groupBound
  nlinarith only [bounded,inside]

end Counting.HardnessNetworkMachine
