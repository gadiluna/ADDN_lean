import Counting.HardnessNetworkMachineMatrixHead
import Counting.StackUnaryMultiply

namespace Counting.HardnessNetworkMachine
open StackMachine StackMachine.Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

def starRowPositions : Fin 9 ↪ Fin 16 := ⟨![0,1,14,3,4,5,6,7,8],by decide⟩
def MatrixWorkspace.starRow (w : MatrixWorkspace extra) : RowWorkspace (extra+7) := starRowPositions.trans w

def starScratch : List (Fin 16) := [1,3,4,5,6,7,8,12,14]

def emitStarMatrix (extra : Nat) (w : MatrixWorkspace extra) : Routine (extra+14) :=
  sequence (emitMatrixHead extra w)
    (sequence (emitOneHotRow (extra+7) w.starRow)
      (sequence (ofProgram (ListPrograms.copyProgram (extra+13) (w 0) (w 12) (w 4)))
        (sequence (discardBit (w 12))
          (sequence (repeatedCopy (extra+13) (w 14) (w 12) (w 2) (w 4)) (clear (w 14))))))

def starCost (width leaderLength : Nat) :=
  let rowLength:=((Encoding.list Encoding.natural).encode (oneHotRow width 0)).length
  130*(width+1)^2+5*leaderLength+5*width+(5*rowLength+4)*(width-1)+rowLength+20

theorem copies_encoded_reverse {α : Type} (codec : Encoding.Codec α) (value : α) (count : Nat) :
    copies count (codec.encode value).reverse=(Encoding.sequence codec (List.replicate count value)).reverse := by
  induction count with
  | zero=>rfl
  | succ count ih=>rw [copies_succ,ih,List.replicate_succ,Encoding.sequence,List.reverse_append]

/-- Emit the last star round from its cached leader row and measured number
of agents. Every repeated nonleader row is physically copied. -/
theorem emitStarMatrix_executes (extra : Nat) (w : MatrixWorkspace extra)
    (store : Fin (extra+16) → List Bool) (leader : List Nat) (positive : 0<(store (w 0)).length)
    (leaderCode : store (w 13)=((Encoding.list Encoding.natural).encode leader).reverse)
    (empty : ∀ i∈starScratch,store (w i)=[]) :
    ∃ time ≤ starCost (store (w 0)).length (store (w 13)).length,
      Executes (emitStarMatrix extra w) store time
        (Function.update store (w 2)
          (((Encoding.list (Encoding.list Encoding.natural)).encode
            (leader::List.replicate ((store (w 0)).length-1) (oneHotRow (store (w 0)).length 0))).reverse++store (w 2))) := by
  let N:=(store (w 0)).length
  let row:=(Encoding.list Encoding.natural).encode (oneHotRow N 0)
  obtain ⟨headTime,headBound,headRun⟩:=emitMatrixHead_executes extra w store
    (by intro i member;simp only [List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl|rfl|rfl|rfl
        all_goals exact empty _ (by simp [starScratch]))
  let headed:=Function.update store (w 2) (store (w 13)++(Encoding.natural.encode N).reverse++store (w 2))
  have headedEmpty (i : Fin 16) (member : i∈starScratch) : headed (w i)=[] := by
    have ne : i≠2 := by intro eq;subst i;simp [starScratch] at member
    simpa [headed,w.injective.eq_iff,ne] using empty i member
  obtain ⟨rowTime,rowBound,rowRun⟩:=emitOneHotRow_executes (extra+7) w.starRow headed
    (by simpa [MatrixWorkspace.starRow,starRowPositions,headed,w.injective.eq_iff,empty,starScratch] using positive)
    (by intro i member;simp only [rowScratch,List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl|rfl|rfl|rfl|rfl|rfl
        all_goals simp [MatrixWorkspace.starRow,starRowPositions,headed,w.injective.eq_iff,empty,starScratch])
  let rowed:=Function.update headed (w 14) row.reverse
  have rowAs : Executes (emitOneHotRow (extra+7) w.starRow) headed rowTime rowed := by
    simpa [MatrixWorkspace.starRow,starRowPositions,headed,w.injective.eq_iff,empty,starScratch,rowed,row,N] using rowRun
  have copying:=copy_executes (extra+13) (w 0) (w 12) (w 4)
    (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) rowed
    (by simp [rowed,w.injective.eq_iff,headedEmpty,starScratch])
  have input : rowed (w 0)=store (w 0) := by simp [rowed,headed,w.injective.eq_iff]
  have countEmpty : rowed (w 12)=[] := by simp [rowed,w.injective.eq_iff,headedEmpty,starScratch]
  rw [input,countEmpty,List.append_nil] at copying
  let copied:=Function.update rowed (w 12) (store (w 0))
  have dropping:=discardBit_executes (w 12) copied
  let ready:=Function.update rowed (w 12) (store (w 0)).tail
  have dropped : Function.update copied (w 12) (copied (w 12)).tail=ready := by simp [copied,ready]
  rw [dropped] at dropping
  have repeating:=repeatedCopy_executes (extra+13) (w 14) (w 12) (w 2) (w 4)
    (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff])
    (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff])
    (store (w 0)).tail ready (by simp [ready]) (by simp [ready,rowed,w.injective.eq_iff,headedEmpty,starScratch])
  let repeated:=Function.update (Function.update ready (w 12) []) (w 2)
    ((Encoding.sequence (Encoding.list Encoding.natural) (List.replicate (N-1) (oneHotRow N 0))).reverse++headed (w 2))
  have repeatingAs : Executes (repeatedCopy (extra+13) (w 14) (w 12) (w 2) (w 4)) ready
      ((5*row.length+4)*(N-1)+1) repeated := by
    simpa [ready,rowed,w.injective.eq_iff,repeated,row,N,copies_encoded_reverse] using repeating
  have clearing:=clear_executes (w 14) repeated
  have rowAt : repeated (w 14)=row.reverse := by simp [repeated,ready,rowed,w.injective.eq_iff]
  rw [rowAt,List.length_reverse] at clearing
  have final : Function.update repeated (w 14) []=
      Function.update store (w 2)
        (((Encoding.list (Encoding.list Encoding.natural)).encode
          (leader::List.replicate (N-1) (oneHotRow N 0))).reverse++store (w 2)) := by
    have rowCount : (leader::List.replicate (N-1) (oneHotRow N 0)).length=N := by simp;omega
    have encoding : (Encoding.list (Encoding.list Encoding.natural)).encode
          (leader::List.replicate (N-1) (oneHotRow N 0))=
        Encoding.natural.encode N++(Encoding.list Encoding.natural).encode leader++
          Encoding.sequence (Encoding.list Encoding.natural) (List.replicate (N-1) (oneHotRow N 0)) := by
      change Encoding.natural.encode (leader::List.replicate (N-1) (oneHotRow N 0)).length++_=_
      rw [rowCount];simp only [Encoding.sequence,List.append_assoc]
    rw [encoding]
    funext r
    by_cases e14 : r=w 14
    · subst r;simp [w.injective.eq_iff,empty,starScratch]
    · by_cases e12 : r=w 12
      · subst r;simp [repeated,w.injective.eq_iff,empty,starScratch]
      · by_cases e2 : r=w 2
        · subst r;simp [repeated,headed,w.injective.eq_iff,leaderCode,List.reverse_append,List.append_assoc]
        · simp [repeated,ready,rowed,headed,e14,e12,e2]
  rw [final] at clearing
  have combined:=headRun.sequence (rowAs.sequence (copying.sequence (dropping.sequence (repeatingAs.sequence clearing))))
  refine ⟨_,?_,combined⟩
  have rowLimit : rowTime ≤ 100*(N+1)^2 := by
    simpa [MatrixWorkspace.starRow,starRowPositions,headed,w.injective.eq_iff,empty,starScratch,N] using rowBound
  change headTime ≤ 30*(N+1)^2+5*(store (w 13)).length+3 at headBound
  change _ ≤ 130*(N+1)^2+5*(store (w 13)).length+5*N+(5*row.length+4)*(N-1)+row.length+20
  change headTime+1+(rowTime+1+(5*N+2+1+(1+1+((5*row.length+4)*(N-1)+1+1+(row.length+1))))) ≤ _
  omega

end Counting.HardnessNetworkMachine
