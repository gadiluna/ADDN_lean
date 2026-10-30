import Counting.HardnessNetworkMachineBaselineGroup
import Counting.HardnessNetworkMachineRemainingGroups

namespace Counting.HardnessNetworkMachine
open StackMachine StackMachine.Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

theorem consecutiveRows_length (width start count : Nat) :
    (consecutiveRows width start count).length=count := by
  induction count generalizing start with
  | zero=>rfl
  | succ count ih=>simp [consecutiveRows,ih]

theorem groupRows_length (width start size : Nat) (positive : 0<size) :
    (groupRows width start size).length=size := by
  simp [groupRows,consecutiveRows_length];omega

theorem ordinaryGroupRows_length (width start size count : Nat) (positive : 0<size) :
    (ordinaryGroupRows width start size count).length=count*size := by
  induction count generalizing start with
  | zero=>simp [ordinaryGroupRows]
  | succ count ih=>rw [ordinaryGroupRows_succ,List.length_append,groupRows_length _ _ _ positive,ih];ring

theorem pathMatrix_cons_length (base first : Nat) (rest : List Nat) (positive : 0<base) :
    (pathMatrix base (first::rest)).length=networkOrder base (first::rest) := by
  simp only [pathMatrix,List.tail_cons,List.length_cons,List.length_append,
    groupRows_length _ _ _ (by omega : 0<base+1),ordinaryGroupRows_length _ _ _ _ positive,
    networkOrder,List.length_cons]
  ring

def pathScratch : List (Fin 16) := [1,3,4,5,6,7,8,9,11,12]

def emitPathMatrix (extra : Nat) (w : MatrixWorkspace extra) : Routine (extra+14) :=
  sequence (emitMatrixHead extra w)
    (sequence (emitBaselineGroup extra w) (emitRemainingGroups extra w))

def pathCost (width leaderLength base groups : Nat) :=
  30*(width+1)^2+5*leaderLength+groupCost width (base+1)+
    groups*(groupCost width base+7)+width+30

theorem emitPathMatrix_executes (extra : Nat) (w : MatrixWorkspace extra)
    (store : Fin (extra+16) → List Bool) (base first : Nat) (rest : List Nat) (positive : 0<base)
    (width : (store (w 0)).length=networkOrder base (first::rest))
    (baseValue : store (w 10)=List.replicate base true)
    (countValue : store (w 15)=List.replicate rest.length true)
    (leaderCode : store (w 13)=((Encoding.list Encoding.natural).encode (leaderRow base (first::rest))).reverse)
    (empty : ∀ i∈pathScratch,store (w i)=[]) :
    ∃ time ≤ pathCost (store (w 0)).length (store (w 13)).length base rest.length,
      Executes (emitPathMatrix extra w) store time
        (Function.update store (w 2)
          (((Encoding.list (Encoding.list Encoding.natural)).encode (pathMatrix base (first::rest))).reverse++store (w 2))) := by
  let N:=networkOrder base (first::rest)
  obtain ⟨headTime,headBound,headRun⟩:=emitMatrixHead_executes extra w store
    (by intro i member;simp only [List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl|rfl|rfl|rfl
        all_goals exact empty _ (by simp [pathScratch]))
  let headed:=Function.update store (w 2) (store (w 13)++(Encoding.natural.encode N).reverse++store (w 2))
  have headAs : Executes (emitMatrixHead extra w) store headTime headed := by simpa [headed,width,N] using headRun
  have baselineEmpty (i : Fin 16) (member : i∈baselineGroupScratch) : headed (w i)=[] := by
    have ne : i≠2 := by intro eq;subst i;simp [baselineGroupScratch] at member
    have old : i∈pathScratch := by
      simp only [baselineGroupScratch,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals simp [pathScratch]
    simp [headed,w.injective.eq_iff,ne,empty i old]
  have sizeBound : base+2 ≤ (headed (w 0)).length := by
    simp only [headed,Function.update_of_ne (w.injective.ne (by decide : (0:Fin 16)≠2)),width,networkOrder,List.length_cons]
    nlinarith only [Nat.zero_le (rest.length*base)]
  obtain ⟨baseTime,baseBound,baseRun⟩:=emitBaselineGroup_executes extra w headed base
    (by simp [headed,w.injective.eq_iff,baseValue]) sizeBound baselineEmpty
  let based:=baselineGroupResult w headed base
  have remainingEmpty (i : Fin 16) (member : i∈remainingGroupsScratch) : based (w i)=[] := by
    have a : i≠1 := by intro eq;subst i;simp [remainingGroupsScratch] at member
    have b : i≠2 := by intro eq;subst i;simp [remainingGroupsScratch] at member
    have old : i∈pathScratch := by
      simp only [remainingGroupsScratch,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals simp [pathScratch]
    simp [based,baselineGroupResult,headed,w.injective.eq_iff,a,b,empty i old]
  have restBound : (base+2)+rest.length*base ≤ (based (w 0)).length := by
    simp only [based,baselineGroupResult,headed,Function.update_apply,w.injective.eq_iff,Fin.reduceEq,ite_false,width,networkOrder,List.length_cons]
    nlinarith
  obtain ⟨restTime,restLimit,restRun⟩:=emitRemainingGroups_executes extra w based (base+2) base rest.length positive
    (by simp [based,baselineGroupResult,w.injective.eq_iff,Nat.add_assoc])
    (by simp [based,baselineGroupResult,headed,w.injective.eq_iff,baseValue])
    (by simp [based,baselineGroupResult,headed,w.injective.eq_iff,countValue]) restBound remainingEmpty
  have encoding : (Encoding.list (Encoding.list Encoding.natural)).encode (pathMatrix base (first::rest))=
      Encoding.natural.encode N++(Encoding.list Encoding.natural).encode (leaderRow base (first::rest))++
        Encoding.sequence (Encoding.list Encoding.natural) (groupRows N 1 (base+1))++
        Encoding.sequence (Encoding.list Encoding.natural) (ordinaryGroupRows N (base+2) base rest.length) := by
    change Encoding.natural.encode (pathMatrix base (first::rest)).length++_=_
    rw [pathMatrix_cons_length base first rest positive]
    simp only [pathMatrix,List.tail_cons,Encoding.sequence,sequence_append,List.append_assoc,N]
  have final : Function.update (Function.update based (w 1) []) (w 2)
      ((Encoding.sequence (Encoding.list Encoding.natural)
        (ordinaryGroupRows (based (w 0)).length (base+2) base rest.length)).reverse++based (w 2))=
      Function.update store (w 2)
        (((Encoding.list (Encoding.list Encoding.natural)).encode (pathMatrix base (first::rest))).reverse++store (w 2)) := by
    rw [encoding]
    funext r
    by_cases e1 : r=w 1
    · subst r;simp [w.injective.eq_iff,empty,pathScratch]
    · by_cases e2 : r=w 2
      · subst r;simp [based,baselineGroupResult,headed,w.injective.eq_iff,width,N,leaderCode,List.reverse_append,List.append_assoc]
      · simp [based,baselineGroupResult,headed,e1,e2]
  rw [final] at restRun
  have combined:=headAs.sequence (baseRun.sequence restRun)
  refine ⟨_,?_,combined⟩
  have baseLimit : baseTime ≤ groupCost (store (w 0)).length (base+1)+9 := by simpa [headed,w.injective.eq_iff] using baseBound
  have remainingLimit : restTime ≤ rest.length*(groupCost (store (w 0)).length base+7)+(store (w 0)).length+10 := by
    simpa [based,baselineGroupResult,headed,w.injective.eq_iff] using restLimit
  dsimp only [pathCost]
  omega

end Counting.HardnessNetworkMachine
