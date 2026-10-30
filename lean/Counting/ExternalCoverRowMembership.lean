import Counting.ExternalCoverMatchPrefix
import Counting.ExternalSATHeader

namespace Counting.External.CoverVerification
open StackMachine StackMachine.Routine StackMachine.EncodingPrograms SATVerification CoverMachine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def membershipScratch : List (Fin 48) := [2,3,4,5,6,9,10,11,12,13,14,18,20,22,24,29,30]

def rowMembership (extra : Nat) (w : RowWorkspace extra) : Routine (extra+46) :=
  sequence (readListHeader (extra+31) (satHeaderRoles (extra+16) w.reader 1))
    (sequence (pushBit (w 22) false) (matchPrefix extra w))

theorem rowMembership_executes (extra : Nat) (w : RowWorkspace extra)
    (indices : List Nat) (store : Fin (extra+48) → List Bool) (accepted : Bool) (suffix tail : List Bool)
    (source : store (w 0)=(Encoding.list Encoding.natural).encode indices++suffix)
    (status : store (w 1)=accepted::tail)
    (empty : ∀ i∈membershipScratch,store (w i)=[]) :
    ∃ time ≤  2000*((store (w 0)).length+(store (w 38)).length+1)^3,
      Executes (rowMembership extra w) store time
        (Function.update (Function.update store (w 0) suffix) (w 22) [matchingIndex (store (w 38)) indices]) := by
  let inputSize := (store (w 0)).length
  let rest := Encoding.sequence Encoding.natural indices++suffix
  let prepared := Function.update (Function.update store (w 0) rest) (w 24) (List.replicate indices.length true)
  have headerEmpty (i : Fin 17) (member : i∈({2,3,4,5,8,11,12,13,14,15,16}:Finset (Fin 17))) :
      store ((satHeaderRoles (extra+16) w.reader 1) i)=[] := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp [satHeaderRoles,headerPositions,RowWorkspace.reader,rowReaderPositions,empty,membershipScratch]
  have positive (index : Nat) : 0<(Encoding.natural.encode index).length := by simp [Encoding.natural_length]
  obtain ⟨headerTime,headerBound,headerRun⟩ := readListHeader_canonical (extra+31) (satHeaderRoles (extra+16) w.reader 1)
    store accepted tail status headerEmpty Encoding.natural positive indices suffix source
  change Executes (readListHeader (extra+31) (satHeaderRoles (extra+16) w.reader 1)) store headerTime prepared at headerRun
  let initialized := Function.update prepared (w 22) [false]
  have initializing : Executes (pushBit (w 22) false) prepared 1 initialized := by
    simpa [prepared,w.injective.eq_iff,empty,membershipScratch,initialized] using pushBit_executes (w 22) false prepared
  have restBound : rest.length≤ inputSize := by
    dsimp [inputSize];rw [source]
    change rest.length≤ (Encoding.natural.encode indices.length++Encoding.sequence Encoding.natural indices++suffix).length
    dsimp [rest];simp only [List.length_append];omega
  have initEmpty (i : Fin 48) (member : i∈matchScratch) : initialized (w i)=[] := by
    have a : i≠0 := by intro same;subst i;simp [matchScratch] at member
    have b : i≠24 := by intro same;subst i;simp [matchScratch] at member
    have c : i≠22 := by intro same;subst i;simp [matchScratch] at member
    have included : i∈membershipScratch := by
      simp only [matchScratch,membershipScratch,List.mem_cons,List.not_mem_nil,or_false] at member ⊢
      tauto
    simpa [initialized,prepared,w.injective.eq_iff,a,b,c] using empty i included
  obtain ⟨loopTime,loopBound,loopRun⟩ := matchPrefix_executes extra w indices inputSize initialized accepted false suffix tail []
    (by simp [initialized,prepared,w.injective.eq_iff,rest])
    (by simp [initialized,prepared,w.injective.eq_iff])
    (by simp [initialized,prepared,w.injective.eq_iff,status])
    (by simp [initialized])
    (by simpa [initialized,prepared,w.injective.eq_iff] using restBound) initEmpty
  have restored : matchPrefixResult w initialized indices suffix false []=
      Function.update (Function.update store (w 0) suffix) (w 22) [matchingIndex (store (w 38)) indices] := by
    funext r
    by_cases e0 : r=w 0
    · subst r;simp [matchPrefixResult,w.injective.eq_iff]
    · by_cases e24 : r=w 24
      · subst r;simp [matchPrefixResult,w.injective.eq_iff,empty,membershipScratch]
      · by_cases e22 : r=w 22
        · subst r;simp [matchPrefixResult,initialized,prepared,w.injective.eq_iff]
        · simp [matchPrefixResult,initialized,prepared,e0,e24,e22]
  rw [restored] at loopRun
  have query : initialized (w 38)=store (w 38) := by simp [initialized,prepared,w.injective.eq_iff]
  rw [query] at loopBound
  refine ⟨headerTime+1+(1+1+loopTime),?_,headerRun.sequence (initializing.sequence loopRun)⟩
  have count : indices.length≤ inputSize := by
    have bounded := VerifiedParser.sequence_count_le positive indices
    dsimp [rest] at restBound
    simp only [List.length_append] at restBound
    omega
  let size := inputSize+(store (w 38)).length+1
  change headerTime ≤ 1820*(inputSize+1)^3 at headerBound
  have positiveSize : 1≤ size := by dsimp [size];omega
  have inputBound : inputSize≤ size := by dsimp [size];omega
  have headerLimit : headerTime≤ 1820*size^3 :=
    headerBound.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp [size,inputSize];omega) _))
  have loopLimit : loopTime≤ size*(110*size+2)+1 := by
    apply loopBound.trans
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (count.trans inputBound)) 1
  have square : size^2≤ size^3 := Nat.pow_le_pow_right positiveSize (by decide)
  have linear : size≤ size^2 := Nat.le_self_pow (by decide) _
  change headerTime+1+(1+1+loopTime)≤ 2000*size^3
  nlinarith

@[simp] theorem matchingIndex_natural (element : Nat) (indices : List Nat) :
    matchingIndex (Encoding.natural.encode element) indices=indices.contains element := by
  simp only [matchingIndex,Encoding.natural.injective.eq_iff]
  apply Bool.eq_iff_iff.mpr
  simp [List.any_eq_true]

end Counting.External.CoverVerification
