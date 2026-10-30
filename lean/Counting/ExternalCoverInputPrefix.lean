import Counting.ExternalCoverInputLoop
import Counting.ExternalSATHeader

namespace Counting.External.CoverInputValidation
open StackMachine StackMachine.Routine StackMachine.EncodingPrograms SATVerification MatchingVerification
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

def prefixScratch : List (Fin 32):=tripleScratch++[12,13,14,25,27]

def rowsPrefix (extra : Nat) (w : SATWorkspace extra) : Routine (extra+30) :=
  sequence (readListHeader (extra+15) (satHeaderRoles extra w 2))
    (sequence (ofProgram (ListPrograms.copyProgram (extra+29) (w 25) (w 27) (w 3))) (rowsGuard extra w))

theorem rowsPrefix_executes (extra : Nat) (w : SATWorkspace extra)
    (rows : List RawClause) (bits suffix tail : List Bool)
    (store : Fin (extra+32) → List Bool) (accepted : Bool)
    (source : store (w 0)=(Encoding.list MatchingVerification.clauseCodec).encode rows++suffix)
    (universeInput : store (w 17)=bits) (status : store (w 1)=accepted::tail)
    (empty : ∀ i∈prefixScratch,store (w i)=[]) :
    ∃ time ≤ 9000*((store (w 0)).length+bits.length+1)^5,
      Executes (rowsPrefix extra w) store time
        (Function.update (Function.update (Function.update store (w 25) (List.replicate rows.length true))
          (w 0) suffix) (w 1) ((accepted && rowsRange bits rows)::tail)) := by
  have ne (i j : Fin 32) (h : i≠j) : w i≠w j:=fun same=>h (w.injective same)
  let inputSize:=(store (w 0)).length
  let rest:=Encoding.sequence MatchingVerification.clauseCodec rows++suffix
  let prepared:=Function.update (Function.update store (w 0) rest) (w 25) (List.replicate rows.length true)
  have headerEmpty (i : Fin 17) (member : i∈({2,3,4,5,8,11,12,13,14,15,16}:Finset (Fin 17))) :
      store ((satHeaderRoles extra w 2) i)=[] := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp [satHeaderRoles,headerPositions,empty,prefixScratch,tripleScratch,MatchingInputValidation.indexScratch]
  have positive (row : RawClause) : 0 < (MatchingVerification.clauseCodec.encode row).length := by
    rw [clause_encode,Encoding.list_length]
    omega
  obtain ⟨headerTime,headerBound,headerRun⟩:=readListHeader_canonical (extra+15) (satHeaderRoles extra w 2)
    store accepted tail status headerEmpty MatchingVerification.clauseCodec positive rows suffix source
  change Executes (readListHeader (extra+15) (satHeaderRoles extra w 2)) store headerTime prepared at headerRun
  have copying:=copy_executes (extra+29) (w 25) (w 27) (w 3)
    (ne 25 27 (by decide)) (ne 25 3 (by decide)) (ne 27 3 (by decide)) prepared
    (by simp [prepared,w.injective.eq_iff,empty,prefixScratch,tripleScratch,MatchingInputValidation.indexScratch])
  have countAt : prepared (w 25)=List.replicate rows.length true:=by simp [prepared]
  have targetAt : prepared (w 27)=[]:=by simp [prepared,w.injective.eq_iff,empty,prefixScratch]
  rw [countAt,targetAt,List.append_nil,List.length_replicate] at copying
  let ready:=Function.update prepared (w 27) (List.replicate rows.length true)
  have readyEmpty (i : Fin 32) (member : i∈tripleScratch) : ready (w i)=[] := by
    have n0 : i≠0:=by intro same;subst i;simp [tripleScratch,MatchingInputValidation.indexScratch] at member
    have n25 : i≠25:=by intro same;subst i;simp [tripleScratch,MatchingInputValidation.indexScratch] at member
    have n27 : i≠27:=by intro same;subst i;simp [tripleScratch,MatchingInputValidation.indexScratch] at member
    simpa [ready,prepared,w.injective.eq_iff,n0,n25,n27] using empty i (by simp [prefixScratch,member])
  have restBound : rest.length ≤ inputSize := by
    dsimp [inputSize]
    rw [source]
    change rest.length ≤ ((Encoding.natural.encode rows.length++Encoding.sequence MatchingVerification.clauseCodec rows)++suffix).length
    dsimp [rest]
    simp only [List.length_append]
    omega
  obtain ⟨loopTime,loopBound,loopRun⟩:=rowsGuard_executes extra w rows bits suffix tail inputSize ready accepted
    (by simp [ready,prepared,w.injective.eq_iff,rest])
    (by simpa only [ready,prepared,Function.update_of_ne (ne 0 27 (by decide)),Function.update_of_ne (ne 0 25 (by decide)),Function.update_self] using restBound)
    (by simp [ready,prepared,w.injective.eq_iff,universeInput]) (by simp [ready])
    (by simp [ready,prepared,w.injective.eq_iff,status]) readyEmpty
  have final : Function.update (Function.update (Function.update ready (w 27) []) (w 0) suffix)
      (w 1) ((accepted && rowsRange bits rows)::tail)=
      Function.update (Function.update (Function.update store (w 25) (List.replicate rows.length true))
        (w 0) suffix) (w 1) ((accepted && rowsRange bits rows)::tail) := by
    funext r
    by_cases n1 : r=w 1
    · subst r;simp
    · by_cases n0 : r=w 0
      · subst r;simp [w.injective.eq_iff]
      · by_cases n27 : r=w 27
        · subst r;simp [w.injective.eq_iff,empty,prefixScratch]
        · by_cases n25 : r=w 25
          · subst r;simp [ready,prepared,w.injective.eq_iff]
          · simp [ready,prepared,n0,n1,n25,n27]
  rw [final] at loopRun
  refine ⟨headerTime+1+(5*rows.length+2+1+loopTime),?_,headerRun.sequence (copying.sequence loopRun)⟩
  let S:=inputSize+bits.length+1
  have pos : 1 ≤ S:=by dsimp [S];omega
  have countBound:=VerifiedParser.sequence_count_le positive rows
  have rowBound : rows.length ≤ inputSize:=by dsimp [rest] at restBound;simp only [List.length_append] at restBound;omega
  have rowS : rows.length ≤ S:=by dsimp [S];omega
  have headerBig : headerTime ≤ 1820*S^3:=by
    change headerTime ≤ 1820*(inputSize+1)^3 at headerBound
    apply headerBound.trans
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    dsimp [S,inputSize];omega
  have cubic : S^3 ≤ S^5:=Nat.pow_le_pow_right pos (by decide)
  have fourth : S^4 ≤ S^5:=Nat.pow_le_pow_right pos (by decide)
  have linear : S ≤ S^5:=Nat.le_self_pow (by decide) S
  have loopBig : loopTime ≤ 1300*S^4+2*S+1 := by
    calc
      _ ≤ rows.length*(1300*S^3+2)+1:=loopBound
      _ ≤ S*(1300*S^3+2)+1:=by gcongr
      _ = _:=by ring
  change _ ≤ 9000*S^5
  nlinarith only [headerBig,cubic,linear,loopBig,fourth,rowS,Nat.one_le_pow 5 S pos]

end Counting.External.CoverInputValidation
