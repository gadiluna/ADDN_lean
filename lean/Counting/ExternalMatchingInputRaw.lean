import Counting.ExternalMatchingInputPrefix
import Counting.StackBooleanPrefix
import Counting.StackEmitSyntax

namespace Counting.External.MatchingInputValidation
open StackMachine StackMachine.Routine StackMachine.EncodingPrograms SATVerification MatchingVerification
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

def rawStatus (raw : MatchingVerification.Raw) : Bool :=
  raw.1.all id && rowsRange (List.replicate raw.1.length true) raw.2

theorem rawStatus_eq (raw : MatchingVerification.Raw) :
    rawStatus raw=validRaw (MatchingVerification.toRaw raw) := by
  have same : rowRange (List.replicate raw.1.length true)=
      (fun row : RawClause=>(clauseToRaw row).length==3 &&
        (clauseToRaw row).all (fun value=>decide (value < raw.1.length))) := by
    funext row
    simp [rowRange,clauseToRaw]
  simp only [rawStatus,validRaw,MatchingVerification.toRaw,rowsRange,List.all_map,same]
  rfl

def rawScratch : List (Fin 32):=prefixScratch++[17]

def rawGuard (extra : Nat) (w : SATWorkspace extra) : Routine (extra+30) :=
  sequence (readListHeader (extra+15) (satHeaderRoles extra w 2))
    (sequence (ofProgram (ListPrograms.copyProgram (extra+29) (w 25) (w 17) (w 3)))
      (sequence (BooleanFold.prefixRoutine .conjunction (w 0) (w 1) (w 25)) (rowsPrefix extra w)))

theorem rawGuard_executes (extra : Nat) (w : SATWorkspace extra)
    (raw : MatchingVerification.Raw) (suffix tail : List Bool)
    (store : Fin (extra+32) → List Bool) (accepted : Bool)
    (source : store (w 0)=MatchingVerification.rawCodec.encode raw++suffix)
    (status : store (w 1)=accepted::tail)
    (empty : ∀ i∈rawScratch,store (w i)=[]) :
    ∃ time ≤ 230000*((store (w 0)).length+1)^5,
      Executes (rawGuard extra w) store time
        (Function.update (Function.update (Function.update (Function.update store
          (w 17) (List.replicate raw.1.length true)) (w 25) (List.replicate raw.2.length true))
          (w 0) suffix) (w 1) ((accepted && rawStatus raw)::tail)) := by
  have ne (i j : Fin 32) (h : i≠j) : w i≠w j:=fun same=>h (w.injective same)
  let rest:=(Encoding.list MatchingVerification.clauseCodec).encode raw.2++suffix
  let prepared:=Function.update (Function.update store (w 0) (raw.1++rest)) (w 25) (List.replicate raw.1.length true)
  have headerEmpty (i : Fin 17) (member : i∈({2,3,4,5,8,11,12,13,14,15,16}:Finset (Fin 17))) :
      store ((satHeaderRoles extra w 2) i)=[] := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp [satHeaderRoles,headerPositions,empty,rawScratch,prefixScratch,indexScratch]
  obtain ⟨headerTime,headerBound,headerRun⟩:=readListHeader_canonical (extra+15) (satHeaderRoles extra w 2)
    store accepted tail status headerEmpty Encoding.boolean (by intro bit;simp [Encoding.boolean]) raw.1 rest
    (by
      change store (w 0)=(Encoding.list Encoding.boolean).encode raw.1++rest
      simpa only [MatchingVerification.rawCodec,Encoding.product,List.append_assoc,rest] using source)
  change Executes (readListHeader (extra+15) (satHeaderRoles extra w 2)) store headerTime
    (Function.update (Function.update store (w 0) (Encoding.sequence Encoding.boolean raw.1++rest))
      (w 25) (List.replicate raw.1.length true)) at headerRun
  rw [sequence_boolean] at headerRun
  have copying:=copy_executes (extra+29) (w 25) (w 17) (w 3)
    (ne 25 17 (by decide)) (ne 25 3 (by decide)) (ne 17 3 (by decide)) prepared
    (by simp [prepared,w.injective.eq_iff,empty,rawScratch,prefixScratch,indexScratch])
  have countAt : prepared (w 25)=List.replicate raw.1.length true:=by simp [prepared]
  have targetAt : prepared (w 17)=[]:=by simp [prepared,w.injective.eq_iff,empty,rawScratch]
  rw [countAt,targetAt,List.append_nil,List.length_replicate] at copying
  let copied:=Function.update prepared (w 17) (List.replicate raw.1.length true)
  have markersRun:=BooleanFold.markers_executes (w 0) (w 1) (w 25)
    (ne 0 1 (by decide)) (ne 0 25 (by decide)) (ne 1 25 (by decide)) copied raw.1 rest accepted tail
    (by simp [copied,prepared,w.injective.eq_iff]) (by simp [copied,prepared,w.injective.eq_iff,status])
    (by simp [copied,prepared,w.injective.eq_iff])
  let marked:=BooleanFold.prefixStore (w 0) (w 1) (w 25) copied rest (accepted && raw.1.all id) tail
  have markedEmpty (i : Fin 32) (member : i∈prefixScratch) : marked (w i)=[] := by
    have n0 : i≠0:=by intro same;subst i;simp [prefixScratch,indexScratch] at member
    have n1 : i≠1:=by intro same;subst i;simp [prefixScratch,indexScratch] at member
    have n17 : i≠17:=by intro same;subst i;simp [prefixScratch,indexScratch] at member
    by_cases n25 : i=25
    · subst i;simp [marked,BooleanFold.prefixStore,w.injective.eq_iff]
    · simpa [marked,BooleanFold.prefixStore,copied,prepared,w.injective.eq_iff,n0,n1,n17,n25] using
        empty i (by simp [rawScratch,member])
  obtain ⟨rowsTime,rowsBound,rowsRun⟩:=rowsPrefix_executes extra w raw.2 (List.replicate raw.1.length true)
    suffix tail marked (accepted && raw.1.all id)
    (by simp [marked,BooleanFold.prefixStore,w.injective.eq_iff,rest])
    (by simp [marked,BooleanFold.prefixStore,copied,w.injective.eq_iff])
    (by simp [marked,BooleanFold.prefixStore]) markedEmpty
  have final : Function.update (Function.update (Function.update marked (w 25) (List.replicate raw.2.length true))
      (w 0) suffix) (w 1) (((accepted && raw.1.all id) && rowsRange (List.replicate raw.1.length true) raw.2)::tail)=
      Function.update (Function.update (Function.update (Function.update store
        (w 17) (List.replicate raw.1.length true)) (w 25) (List.replicate raw.2.length true))
        (w 0) suffix) (w 1) ((accepted && rawStatus raw)::tail) := by
    funext r
    by_cases n1 : r=w 1
    · subst r;simp [rawStatus,Bool.and_assoc]
    · by_cases n0 : r=w 0
      · subst r;simp [w.injective.eq_iff]
      · by_cases n25 : r=w 25
        · subst r;simp [w.injective.eq_iff]
        · by_cases n17 : r=w 17
          · subst r;simp [marked,BooleanFold.prefixStore,copied,w.injective.eq_iff]
          · simp [marked,BooleanFold.prefixStore,copied,prepared,n0,n1,n17,n25]
  rw [final] at rowsRun
  have combined:=headerRun.sequence (copying.sequence (markersRun.sequence rowsRun))
  refine ⟨headerTime+1+(5*raw.1.length+2+1+(5*raw.1.length+1+1+rowsTime)),?_,combined⟩
  let L:=(store (w 0)).length
  have sourceAs : store (w 0)=(Encoding.natural.encode raw.1.length++raw.1)++rest := by
    simpa only [MatchingVerification.rawCodec,Encoding.product,Encoding.list,sequence_boolean,List.append_assoc,rest] using source
  have split : L=(Encoding.natural.encode raw.1.length).length+raw.1.length+rest.length := by
    dsimp [L];rw [sourceAs];simp only [List.length_append]
  have markerBound : raw.1.length ≤ L:=by omega
  have restBound : rest.length ≤ L:=by omega
  have markedSource : marked (w 0)=rest:=by simp [marked,BooleanFold.prefixStore,w.injective.eq_iff]
  rw [markedSource,List.length_replicate] at rowsBound
  have power : (rest.length+raw.1.length+1)^5 ≤ 32*(L+1)^5 := by
    calc
      _ ≤ (2*(L+1))^5:=Nat.pow_le_pow_left (by omega) 5
      _ = _:=by ring
  have rowsBig : rowsTime ≤ 224000*(L+1)^5 := by
    have h:=rowsBound.trans (Nat.mul_le_mul_left 7000 power)
    nlinarith only [h]
  change headerTime ≤ 1820*(L+1)^3 at headerBound
  have cube : (L+1)^3 ≤ (L+1)^5:=Nat.pow_le_pow_right (by omega) (by decide)
  have headerBig:=headerBound.trans (Nat.mul_le_mul_left 1820 cube)
  have linear : L+1 ≤ (L+1)^5:=Nat.le_self_pow (by decide) _
  change _ ≤ 230000*(L+1)^5
  nlinarith only [headerBig,rowsBig,markerBound,linear]

end Counting.External.MatchingInputValidation
