import Counting.HardnessNetworkMachineValues

namespace Counting.HardnessNetworkMachine
open StackMachine StackMachine.Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

abbrev GroupWorkspace (extra : Nat) := Fin 12 ↪ Fin (extra+12)
def groupRowsPositions : Fin 10 ↪ Fin 12 :=
  ⟨fun i=>⟨i.val,by omega⟩,by intro a b h;exact Fin.ext (congrArg (fun i : Fin 12=>i.val) h)⟩
def GroupWorkspace.rows (w : GroupWorkspace extra) : RowsWorkspace (extra+2) := groupRowsPositions.trans w
def groupZeroPositions : Fin 9 ↪ Fin 12 := ⟨![0,11,2,3,4,5,6,7,8],by decide⟩
def GroupWorkspace.zero (w : GroupWorkspace extra) : RowWorkspace (extra+3) := groupZeroPositions.trans w

def groupScratch : List (Fin 12) := [3,4,5,6,7,8,9,11]

def emitGroup (extra : Nat) (w : GroupWorkspace extra) : Routine (extra+10) :=
  sequence (ofProgram (ListPrograms.copyProgram (extra+9) (w 10) (w 9) (w 4)))
    (sequence (discardBit (w 9))
      (sequence (emitConsecutiveRows (extra+2) w.rows)
        (sequence (emitOneHotRow (extra+3) w.zero) (pushBit (w 1) true))))

def groupCost (width size : Nat) :=
  5*size+(size-1)*(100*(2*width+1)^2+4)+100*(width+1)^2+10

def groupResult (w : GroupWorkspace extra) (store : Fin (extra+12) → List Bool) (start size : Nat) :=
  Function.update (Function.update store (w 1) (List.replicate size true++store (w 1))) (w 2)
    ((Encoding.sequence (Encoding.list Encoding.natural) (groupRows (store (w 0)).length start size)).reverse++store (w 2))

/-- Emit all nonleader rows of one group, including the final edge back to
the leader. The next-column index advances to the following group's start. -/
theorem emitGroup_executes (extra : Nat) (w : GroupWorkspace extra) (start size : Nat)
    (store : Fin (extra+12) → List Bool) (positive : 0<size)
    (index : (store (w 1)).length=start+1)
    (counter : store (w 10)=List.replicate size true)
    (inside : start+size ≤ (store (w 0)).length)
    (empty : ∀ i∈groupScratch,store (w i)=[]) :
    ∃ time ≤ groupCost (store (w 0)).length size,
      Executes (emitGroup extra w) store time (groupResult w store start size) := by
  have copying:=copy_executes (extra+9) (w 10) (w 9) (w 4)
    (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) store
    (empty 4 (by simp [groupScratch]))
  rw [counter,empty 9 (by simp [groupScratch]),List.append_nil,List.length_replicate] at copying
  let copied:=Function.update store (w 9) (List.replicate size true)
  have skipping:=discardBit_executes (w 9) copied
  let ready:=Function.update store (w 9) (List.replicate (size-1) true)
  have skipped : Function.update copied (w 9) (copied (w 9)).tail=ready := by simp [copied,ready,List.tail_replicate]
  rw [skipped] at skipping
  have rowsEmpty (i : Fin 10) (member : i∈([3,4,5,6,7,8] : List (Fin 10))) : ready (w.rows i)=[] := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp [GroupWorkspace.rows,groupRowsPositions,ready,w.injective.eq_iff,empty,groupScratch]
  obtain ⟨rowsTime,rowsBound,rowsRun⟩:=emitConsecutiveRows_executes (extra+2) w.rows (size-1) ready
    (by simp [GroupWorkspace.rows,groupRowsPositions,ready])
    (by change (ready (w 1)).length+(size-1) ≤ (ready (w 0)).length
        simp only [ready,Function.update_apply,w.injective.eq_iff,Fin.reduceEq,ite_false]
        omega) rowsEmpty
  let afterRows:=consecutiveRowsResult w.rows ready (size-1)
  have zeroEmpty (i : Fin 9) (member : i∈rowScratch) : afterRows (w.zero i)=[] := by
    simp only [rowScratch,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp [afterRows,consecutiveRowsResult,GroupWorkspace.rows,groupRowsPositions,GroupWorkspace.zero,groupZeroPositions,
      ready,w.injective.eq_iff,empty,groupScratch]
  have zeroInside : (afterRows (w.zero 1)).length<(afterRows (w.zero 0)).length := by
    simp [afterRows,consecutiveRowsResult,GroupWorkspace.rows,groupRowsPositions,GroupWorkspace.zero,groupZeroPositions,
      ready,w.injective.eq_iff,empty,groupScratch]
    omega
  obtain ⟨zeroTime,zeroBound,zeroRun⟩:=emitOneHotRow_executes (extra+3) w.zero afterRows zeroInside zeroEmpty
  let afterZero:=Function.update afterRows (w 2)
    (((Encoding.list Encoding.natural).encode (oneHotRow (store (w 0)).length 0)).reverse++afterRows (w 2))
  have zeroAs : Executes (emitOneHotRow (extra+3) w.zero) afterRows zeroTime afterZero := by
    simpa [afterZero,afterRows,consecutiveRowsResult,GroupWorkspace.rows,groupRowsPositions,GroupWorkspace.zero,groupZeroPositions,
      ready,w.injective.eq_iff,empty,groupScratch] using zeroRun
  have pushing:=pushBit_executes (w 1) true afterZero
  have final : Function.update afterZero (w 1) (true::afterZero (w 1))=groupResult w store start size := by
    funext r
    by_cases e1 : r=w 1
    · subst r
      have sizes : size-1+1=size := by omega
      have sequence : true::(List.replicate (size-1) true++store (w 1))=List.replicate size true++store (w 1) := by
        rw [←List.cons_append,←List.replicate_succ,sizes]
      simpa [afterZero,afterRows,consecutiveRowsResult,GroupWorkspace.rows,groupRowsPositions,
        ready,groupResult,w.injective.eq_iff] using sequence
    · by_cases e2 : r=w 2
      · subst r
        simp [afterZero,afterRows,consecutiveRowsResult,groupResult,groupRows,GroupWorkspace.rows,groupRowsPositions,
          ready,w.injective.eq_iff,index,sequence_append,Encoding.sequence,List.reverse_append,List.append_assoc]
      · by_cases e9 : r=w 9
        · subst r;simp [afterZero,afterRows,consecutiveRowsResult,groupResult,GroupWorkspace.rows,groupRowsPositions,
            ready,w.injective.eq_iff,empty,groupScratch]
        · simp [afterZero,afterRows,consecutiveRowsResult,groupResult,GroupWorkspace.rows,groupRowsPositions,
            ready,e1,e2,e9]
  rw [final] at pushing
  have combined:=copying.sequence (skipping.sequence (rowsRun.sequence (zeroAs.sequence pushing)))
  refine ⟨_,?_,combined⟩
  have rowLimit : rowsTime ≤ (size-1)*(100*(2*(store (w 0)).length+1)^2+4)+1 := by
    simpa [GroupWorkspace.rows,groupRowsPositions,ready,w.injective.eq_iff] using rowsBound
  have zeroLimit : zeroTime ≤ 100*((store (w 0)).length+1)^2 := by
    simpa [afterRows,consecutiveRowsResult,GroupWorkspace.rows,groupRowsPositions,GroupWorkspace.zero,groupZeroPositions,
      ready,w.injective.eq_iff,empty,groupScratch] using zeroBound
  dsimp only [groupCost]
  omega

end Counting.HardnessNetworkMachine
