import Counting.ExternalCNFMeasureFormula
import Counting.StackBooleanPrefix
import Counting.StackEmitSyntax
import Counting.ExternalSATSemantics

namespace Counting.External.CNFMachine
open StackMachine StackMachine.Routine StackMachine.EncodingPrograms SATVerification
set_option backward.isDefEq.respectTransparency false

def rawMeasureScratch : List (Fin 32) := measureScratch++[17,31]

def measureRaw (extra : Nat) (w : SATWorkspace extra) : Routine (extra+30) :=
  sequence (readListHeader (extra+15) (satHeaderRoles extra w 2))
    (sequence (ofProgram (ListPrograms.copyProgram (extra+29) (w 25) (w 17) (w 3)))
      (sequence (BooleanFold.prefixRoutine .conjunction (w 0) (w 1) (w 25)) (measureFormula extra w)))

theorem formulaRange_replicate (n : Nat) (clauses : List (List (Nat×Bool))) :
    formulaRange (List.replicate n true) clauses=
      clauses.all (fun clause => clause.all (fun literal => decide (literal.1<n))) := by
  apply Bool.eq_iff_iff.mpr
  simp [formulaRange,clauseRange]

/-- Actual parsing, range validation, and unary measurements n,m,W. The
counters are bounded by the explicitly encoded table and clause occurrences;
no binary number is expanded without an input-length budget. -/
theorem measureRaw_executes (extra : Nat) (w : SATWorkspace extra)
    (raw : CNFEncoding.Raw) (suffix tail : List Bool)
    (store : Fin (extra+32) → List Bool) (accepted : Bool)
    (source : store (w 0)=CNFEncoding.rawCodec.encode raw++suffix)
    (status : store (w 1)=accepted::tail)
    (empty : ∀ i∈rawMeasureScratch,store (w i)=[]) :
    ∃ time ≤ 230000*((store (w 0)).length+1)^5,
      Executes (measureRaw extra w) store time
        (Function.update (Function.update (Function.update (Function.update (Function.update store
          (w 17) (List.replicate raw.1.length true)) (w 25) (List.replicate raw.2.length true))
          (w 31) (List.replicate (rawWidth raw.2) true)) (w 0) suffix)
          (w 1) ((accepted && validRaw raw)::tail)) := by
  have ne (i j : Fin 32) (h : i≠j) : w i≠w j := fun same => h (w.injective same)
  let rest := (Encoding.list (Encoding.list (Encoding.product Encoding.natural Encoding.boolean))).encode raw.2++suffix
  let prepared := Function.update (Function.update store (w 0) (raw.1++rest)) (w 25) (List.replicate raw.1.length true)
  have headerEmpty (i : Fin 17) (member : i∈({2,3,4,5,8,11,12,13,14,15,16}:Finset (Fin 17))) :
      store ((satHeaderRoles extra w 2) i)=[] := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp [satHeaderRoles,headerPositions,empty,rawMeasureScratch,measureScratch,formulaScratch,clauseScratch]
  obtain ⟨headerTime,headerBound,headerRun⟩ := readListHeader_canonical (extra+15) (satHeaderRoles extra w 2)
    store accepted tail status headerEmpty Encoding.boolean (by intro bit;simp [Encoding.boolean]) raw.1 rest
    (by
      change store (w 0)=(Encoding.list Encoding.boolean).encode raw.1++rest
      simpa only [CNFEncoding.rawCodec,Encoding.product,List.append_assoc,rest] using source)
  change Executes (readListHeader (extra+15) (satHeaderRoles extra w 2)) store headerTime
    (Function.update (Function.update store (w 0) (Encoding.sequence Encoding.boolean raw.1++rest))
      (w 25) (List.replicate raw.1.length true)) at headerRun
  rw [sequence_boolean] at headerRun
  have copying := copy_executes (extra+29) (w 25) (w 17) (w 3)
    (ne 25 17 (by decide)) (ne 25 3 (by decide)) (ne 17 3 (by decide)) prepared
    (by simp [prepared,w.injective.eq_iff,empty,rawMeasureScratch,measureScratch,formulaScratch,clauseScratch])
  have preparedCount : prepared (w 25)=List.replicate raw.1.length true := by simp [prepared]
  have preparedTarget : prepared (w 17)=[] := by simp [prepared,w.injective.eq_iff,empty,rawMeasureScratch]
  rw [preparedCount,preparedTarget,List.append_nil,List.length_replicate] at copying
  let copied := Function.update prepared (w 17) (List.replicate raw.1.length true)
  have markersRun := BooleanFold.markers_executes (w 0) (w 1) (w 25)
    (ne 0 1 (by decide)) (ne 0 25 (by decide)) (ne 1 25 (by decide)) copied raw.1 rest accepted tail
    (by simp [copied,prepared,w.injective.eq_iff]) (by simp [copied,prepared,w.injective.eq_iff,status])
    (by simp [copied,prepared,w.injective.eq_iff])
  let marked := BooleanFold.prefixStore (w 0) (w 1) (w 25) copied rest (accepted && raw.1.all id) tail
  have markedEmpty (i : Fin 32) (member : i∈measureScratch) : marked (w i)=[] := by
    have a : i≠0 := by intro same;subst i;simp [measureScratch,formulaScratch,clauseScratch] at member
    have b : i≠1 := by intro same;subst i;simp [measureScratch,formulaScratch,clauseScratch] at member
    have c : i≠17 := by intro same;subst i;simp [measureScratch,formulaScratch,clauseScratch] at member
    by_cases d : i=25
    · subst i;simp [marked,BooleanFold.prefixStore,w.injective.eq_iff]
    · simpa [marked,BooleanFold.prefixStore,copied,prepared,w.injective.eq_iff,a,b,c,d] using
        empty i (by simp [rawMeasureScratch,member])
  obtain ⟨formulaTime,formulaBound,formulaRun⟩ := measureFormula_executes extra w raw.2
    (List.replicate raw.1.length true) suffix tail marked (accepted && raw.1.all id)
    (by simp [marked,BooleanFold.prefixStore,w.injective.eq_iff,rest])
    (by simp [marked,BooleanFold.prefixStore,copied,w.injective.eq_iff])
    (by simp [marked,BooleanFold.prefixStore]) markedEmpty
  have finalStore : Function.update (Function.update (Function.update (Function.update marked (w 25)
      (List.replicate raw.2.length true)) (w 31) (List.replicate (rawWidth raw.2) true++marked (w 31)))
      (w 0) suffix) (w 1) (((accepted && raw.1.all id) && formulaRange (List.replicate raw.1.length true) raw.2)::tail)=
      Function.update (Function.update (Function.update (Function.update (Function.update store
        (w 17) (List.replicate raw.1.length true)) (w 25) (List.replicate raw.2.length true))
        (w 31) (List.replicate (rawWidth raw.2) true)) (w 0) suffix) (w 1) ((accepted && validRaw raw)::tail) := by
    funext r
    by_cases a : r=w 1
    · subst r;simp [validRaw,formulaRange_replicate,Bool.and_assoc]
    · by_cases b : r=w 0
      · subst r;simp [w.injective.eq_iff]
      · by_cases c : r=w 31
        · subst r;simp [marked,BooleanFold.prefixStore,copied,prepared,w.injective.eq_iff,empty,rawMeasureScratch]
        · by_cases d : r=w 25
          · subst r;simp [w.injective.eq_iff]
          · by_cases e : r=w 17
            · subst r;simp [marked,BooleanFold.prefixStore,copied,w.injective.eq_iff]
            · simp [marked,BooleanFold.prefixStore,copied,prepared,a,b,c,d,e]
  rw [finalStore] at formulaRun
  have combined := headerRun.sequence (copying.sequence (markersRun.sequence formulaRun))
  refine ⟨headerTime+1+(5*raw.1.length+2+1+(5*raw.1.length+1+1+formulaTime)),?_,combined⟩
  let L := (store (w 0)).length
  have encodedSource : store (w 0)=
      (Encoding.natural.encode raw.1.length++Encoding.sequence Encoding.boolean raw.1)++rest := by
    change store (w 0)=((Encoding.natural.encode raw.1.length++Encoding.sequence Encoding.boolean raw.1)++
      (Encoding.list (Encoding.list (Encoding.product Encoding.natural Encoding.boolean))).encode raw.2)++suffix at source
    simpa only [List.append_assoc,rest] using source
  rw [sequence_boolean] at encodedSource
  have split : L=(Encoding.natural.encode raw.1.length).length+raw.1.length+rest.length := by
    dsimp [L];rw [encodedSource];simp only [List.length_append]
  have markerBound : raw.1.length≤L := by omega
  have restBound : rest.length≤L := by omega
  have markedSource : marked (w 0)=rest := by simp [marked,BooleanFold.prefixStore,w.injective.eq_iff]
  rw [markedSource,List.length_replicate] at formulaBound
  have power : (rest.length+raw.1.length+1)^5≤32*(L+1)^5 := by
    calc
      _≤(2*(L+1))^5 := Nat.pow_le_pow_left (by omega) 5
      _=_ := by ring
  have formulaBig : formulaTime≤224000*(L+1)^5 := by
    have h := formulaBound.trans (Nat.mul_le_mul_left 7000 power)
    nlinarith only [h]
  change headerTime≤1820*(L+1)^3 at headerBound
  have cube : (L+1)^3≤(L+1)^5 := Nat.pow_le_pow_right (by omega) (by decide)
  have headerBig := headerBound.trans (Nat.mul_le_mul_left 1820 cube)
  have linear : L+1≤(L+1)^5 := Nat.le_self_pow (by decide) _
  change _≤230000*(L+1)^5
  nlinarith only [headerBig,formulaBig,markerBound,linear]

end Counting.External.CNFMachine
