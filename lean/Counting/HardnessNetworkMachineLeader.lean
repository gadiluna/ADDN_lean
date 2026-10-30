import Counting.HardnessNetworkMachineLeaderPrepare
import Counting.HardnessNetworkMachineValues

namespace Counting.HardnessNetworkMachine
open StackMachine StackMachine.Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def leaderScratch : List (Fin 40) := leaderPrepareScratch++leaderBlockScratch

def emitLeaderRow (extra : Nat) (w : LeaderWorkspace extra) : Routine (extra+38) :=
  sequence (prepareLeaderRow extra w)
    (sequence (emitLeaderFirst extra w) (emitLeaderBlocks extra w))

def leaderRowCost (sourceLength width base groups : Nat) :=
  30*(width+1)^2+1820*(sourceLength+1)^3+(groups+1)*(leaderBlockCost sourceLength (base+1)+6)+20

theorem leaderRow_cons_length (base first : Nat) (rest : List Nat) :
    (leaderRow base (first::rest)).length=2+(rest.length+1)*base := by
  have flat : (rest.flatMap (List.replicate base)).length=rest.length*base := by
    induction rest with
    | nil=>simp
    | cons value values ih=>simp only [List.flatMap_cons,List.length_append,List.length_replicate,ih,List.length_cons];ring
  simp only [leaderRow,List.headD_cons,List.tail_cons,List.length_cons,List.length_append,List.length_replicate,flat]
  ring

/-- Complete binary serialization of the leader's adjacency row, including
its measured row header and the baseline group's extra member. -/
theorem emitLeaderRow_executes (extra : Nat) (w : LeaderWorkspace extra)
    (store : Fin (extra+40) → List Bool) (first : Nat) (rest : List Nat) (accepted : Bool) (suffix tail : List Bool)
    (source : store (w 0)=(Encoding.list Encoding.natural).encode (first::rest)++suffix)
    (status : store (w 1)=accepted::tail)
    (width : (store (w 32)).length=2+(rest.length+1)*(store (w 33)).length)
    (empty : ∀ i∈leaderScratch,store (w i)=[]) :
    ∃ time ≤ leaderRowCost (store (w 0)).length (store (w 32)).length (store (w 33)).length rest.length,
      Executes (emitLeaderRow extra w) store time
        (Function.update (Function.update store (w 0) suffix) (w 35)
          (((Encoding.list Encoding.natural).encode (leaderRow (store (w 33)).length (first::rest))).reverse++store (w 35))) := by
  let S:=(store (w 0)).length
  let B:=(store (w 33)).length
  obtain ⟨prepTime,prepBound,preparing⟩:=prepareLeaderRow_executes extra w store first rest accepted suffix tail source status
    (fun i member=>empty i (List.mem_append_left _ member))
  let prepared:=leaderPrepared w store first rest suffix
  have preparedSource : prepared (w 0)=Encoding.natural.encode first++(Encoding.sequence Encoding.natural rest++suffix) := by
    simp [prepared,leaderPrepared,w.injective.eq_iff,Encoding.sequence,List.append_assoc]
  have preparedEmpty (i : Fin 40) (member : i∈leaderBlockScratch) : prepared (w i)=[] := by
    have a : i≠0 := by intro eq;subst i;simp [leaderBlockScratch] at member
    have b : i≠23 := by intro eq;subst i;simp [leaderBlockScratch] at member
    have c : i≠35 := by intro eq;subst i;simp [leaderBlockScratch] at member
    simp [prepared,leaderPrepared,w.injective.eq_iff,a,b,c,empty i (List.mem_append_right _ member)]
  obtain ⟨firstTime,firstBound,firstRun⟩:=emitLeaderFirst_executes extra w prepared first accepted
    (Encoding.sequence Encoding.natural rest++suffix) tail preparedSource
    (by simp [prepared,leaderPrepared,w.injective.eq_iff,status]) preparedEmpty
  let firstResult:=Function.update (Function.update prepared (w 0) (Encoding.sequence Encoding.natural rest++suffix)) (w 35)
    ((Encoding.sequence Encoding.natural (List.replicate (B+1) first)).reverse++prepared (w 35))
  have firstAs : Executes (emitLeaderFirst extra w) prepared firstTime firstResult := by
    simpa [prepared,leaderPrepared,w.injective.eq_iff,B,firstResult] using firstRun
  have firstEmpty (i : Fin 40) (member : i∈leaderBlockScratch) : firstResult (w i)=[] := by
    have a : i≠0 := by intro eq;subst i;simp [leaderBlockScratch] at member
    have b : i≠35 := by intro eq;subst i;simp [leaderBlockScratch] at member
    simpa [firstResult,w.injective.eq_iff,a,b] using preparedEmpty i member
  have preparedBound : (prepared (w 0)).length ≤ S := by
    simp only [prepared,leaderPrepared,Function.update_apply,w.injective.eq_iff,Fin.reduceEq,ite_false,ite_true]
    dsimp only [S];rw [source];change _ ≤ ((Encoding.natural.encode (first::rest).length++Encoding.sequence Encoding.natural (first::rest))++suffix).length
    simp only [List.length_append];omega
  have firstBoundLength : (firstResult (w 0)).length ≤ S := by
    simp only [firstResult,Function.update_apply,w.injective.eq_iff,Fin.reduceEq,ite_false,ite_true]
    rw [preparedSource] at preparedBound
    simp only [List.length_append] at preparedBound ⊢;omega
  obtain ⟨loopTime,loopBound,loopRun⟩:=emitLeaderBlocks_executes extra w rest S firstResult accepted suffix tail
    (by simp [firstResult,w.injective.eq_iff])
    (by simp [firstResult,prepared,leaderPrepared,w.injective.eq_iff])
    (by simp [firstResult,prepared,leaderPrepared,w.injective.eq_iff,status]) firstBoundLength firstEmpty
  have final : leaderBlocksResult w firstResult rest suffix=
      Function.update (Function.update store (w 0) suffix) (w 35)
        (((Encoding.list Encoding.natural).encode (leaderRow B (first::rest))).reverse++store (w 35)) := by
    have size : (leaderRow B (first::rest)).length=(store (w 32)).length := by
      rw [leaderRow_cons_length,width]
    have encoding : (Encoding.list Encoding.natural).encode (leaderRow B (first::rest))=
        Encoding.natural.encode (store (w 32)).length++[false]++
        Encoding.sequence Encoding.natural (List.replicate (B+1) first)++
        Encoding.sequence Encoding.natural (rest.flatMap (List.replicate B)) := by
      change Encoding.natural.encode (leaderRow B (first::rest)).length++Encoding.sequence Encoding.natural (leaderRow B (first::rest))=_
      rw [size]
      simp only [leaderRow,List.headD_cons,List.tail_cons,Encoding.sequence,sequence_append,List.append_assoc]
      rfl
    rw [encoding]
    funext r
    by_cases e0 : r=w 0
    · subst r;simp [leaderBlocksResult,w.injective.eq_iff]
    · by_cases e23 : r=w 23
      · subst r;simp [leaderBlocksResult,w.injective.eq_iff,empty,leaderScratch,leaderPrepareScratch]
      · by_cases e35 : r=w 35
        · subst r;simp [leaderBlocksResult,firstResult,prepared,leaderPrepared,w.injective.eq_iff,B,List.reverse_append,List.append_assoc]
        · simp [leaderBlocksResult,firstResult,prepared,leaderPrepared,e0,e23,e35,w.injective.eq_iff]
  rw [final] at loopRun
  have combined:=preparing.sequence (firstAs.sequence loopRun)
  refine ⟨_,?_,combined⟩
  have firstLimit : firstTime ≤ leaderBlockCost S (B+1)+4 := by
    apply firstBound.trans
    have baseAt : (prepared (w 33)).length=B := by simp [prepared,leaderPrepared,w.injective.eq_iff,B]
    rw [baseAt]
    dsimp only [leaderBlockCost]
    nlinarith only [Nat.mul_le_mul_right (B+1+1) (Nat.mul_le_mul_left 100 (Nat.add_le_add_right preparedBound 1))]
  have loopLimit : loopTime ≤ rest.length*(leaderBlockCost S (B+1)+2)+1 := by
    apply loopBound.trans
    have baseAt : (firstResult (w 33)).length=B := by simp [firstResult,prepared,leaderPrepared,w.injective.eq_iff,B]
    rw [baseAt]
    apply Nat.add_le_add_right
    apply Nat.mul_le_mul_left
    apply Nat.add_le_add_right
    dsimp only [leaderBlockCost]
    nlinarith
  dsimp only [leaderRowCost]
  change _ ≤ 30*((store (w 32)).length+1)^2+1820*(S+1)^3+(rest.length+1)*(leaderBlockCost S (B+1)+6)+20
  nlinarith only [prepBound,firstLimit,loopLimit]

end Counting.HardnessNetworkMachine
