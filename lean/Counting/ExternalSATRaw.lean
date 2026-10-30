import Counting.ExternalSATSemantics
import Counting.StackBooleanPrefix
import Counting.StackCompareLengthEquality
import Counting.StackEmitSyntax

namespace Counting.External.SATVerification
open StackMachine StackMachine.Routine StackMachine.EncodingPrograms
set_option backward.isDefEq.respectTransparency false

def rawScratch : List (Fin 32) := formulaScratch++[25,29]

def lengthRoles (extra : Nat) (w : SATWorkspace extra) : Fin 6 ↪ Fin (extra+32) :=
  ⟨fun i => w (![17,25,1,26,29,3] i),by
    intro i j same
    have equal := w.injective same
    fin_cases i <;> fin_cases j <;> simp_all⟩

def rawRoutine (extra : Nat) (w : SATWorkspace extra) : Routine (extra+30) :=
  sequence (readListHeader (extra+15) (satHeaderRoles extra w 2))
    (sequence (Compare.preservingLengthEquality (extra+26) (lengthRoles extra w))
      (sequence (ofProgram (combineFlagsProgram (extra+30) (w 1)))
        (sequence (BooleanFold.prefixRoutine .conjunction (w 0) (w 1) (w 25)) (formulaRoutine extra w))))

theorem rawRoutine_executes (extra : Nat) (w : SATWorkspace extra)
    (raw : CNFEncoding.Raw) (bits suffix tail : List Bool)
    (store : Fin (extra+32) → List Bool) (accepted : Bool)
    (source : store (w 0)=CNFEncoding.rawCodec.encode raw++suffix)
    (witness : store (w 17)=bits) (status : store (w 1)=accepted::tail)
    (empty : ∀ i∈rawScratch,store (w i)=[]) :
    ∃ time ≤ 6000*((store (w 0)).length+bits.length+1)^5,
      Executes (rawRoutine extra w) store time
        (Function.update (Function.update store (w 0) suffix)
          (w 1) ((accepted && checkRaw raw bits)::tail)) := by
  have ne (i j : Fin 32) (h : i≠j) : w i≠w j := fun same => h (w.injective same)
  let rest := (Encoding.list (Encoding.list (Encoding.product Encoding.natural Encoding.boolean))).encode raw.2++suffix
  let prepared := Function.update (Function.update store (w 0) (raw.1++rest)) (w 25) (List.replicate raw.1.length true)
  have headerEmpty (i : Fin 17) (member : i∈({2,3,4,5,8,11,12,13,14,15,16}:Finset (Fin 17))) :
      store ((satHeaderRoles extra w 2) i)=[] := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp [satHeaderRoles,headerPositions,empty,rawScratch,formulaScratch,clauseScratch]
  obtain ⟨headerTime,headerBound,headerRun⟩ := readListHeader_canonical (extra+15) (satHeaderRoles extra w 2)
    store accepted tail status headerEmpty Encoding.boolean (by intro bit;simp [Encoding.boolean]) raw.1 rest
    (by
      change store (w 0)=(Encoding.list Encoding.boolean).encode raw.1++rest
      simpa only [CNFEncoding.rawCodec,Encoding.product,List.append_assoc,rest] using source)
  have headerPrepared : Executes (readListHeader (extra+15) (satHeaderRoles extra w 2)) store headerTime prepared := by
    change Executes (readListHeader (extra+15) (satHeaderRoles extra w 2)) store headerTime
      (Function.update (Function.update store (w 0) (Encoding.sequence Encoding.boolean raw.1++rest))
        (w 25) (List.replicate raw.1.length true)) at headerRun
    rw [sequence_boolean] at headerRun
    exact headerRun
  let sizeOk := decide (bits.length=raw.1.length)
  let compared := Function.update prepared (w 1) (sizeOk::accepted::tail)
  have compareRun : Executes (Compare.preservingLengthEquality (extra+26) (lengthRoles extra w)) prepared
      (Compare.preservingLengthEqualityCost bits (List.replicate raw.1.length true)) compared := by
    simpa [lengthRoles,prepared,compared,sizeOk,w.injective.eq_iff,witness,status] using
      Compare.preservingLengthEquality_executes (extra+26) (lengthRoles extra w) prepared
        (by simp [lengthRoles,prepared,w.injective.eq_iff,empty,rawScratch,formulaScratch,clauseScratch])
        (by simp [lengthRoles,prepared,w.injective.eq_iff,empty,rawScratch,formulaScratch,clauseScratch])
        (by simp [lengthRoles,prepared,w.injective.eq_iff,empty,rawScratch,formulaScratch,clauseScratch])
        (by simp [lengthRoles,prepared])
  let sized := Function.update compared (w 1) ((accepted && sizeOk)::tail)
  have combining := combineFlags_executes (extra+30) (w 1) compared accepted sizeOk tail (by simp [compared])
  have markersRun := BooleanFold.markers_executes (w 0) (w 1) (w 25)
    (ne 0 1 (by decide)) (ne 0 25 (by decide)) (ne 1 25 (by decide)) sized raw.1 rest (accepted && sizeOk) tail
    (by simp [sized,compared,prepared,w.injective.eq_iff]) (by simp [sized])
    (by simp [sized,compared,prepared,w.injective.eq_iff])
  let marked := BooleanFold.prefixStore (w 0) (w 1) (w 25) sized rest ((accepted && sizeOk) && raw.1.all id) tail
  have markedEmpty (i : Fin 32) (member : i∈formulaScratch) : marked (w i)=[] := by
    have a : i≠0 := by intro same;subst i;simp [formulaScratch,clauseScratch] at member
    have b : i≠1 := by intro same;subst i;simp [formulaScratch,clauseScratch] at member
    have c : i≠25 := by intro same;subst i;simp [formulaScratch,clauseScratch] at member
    simpa [marked,BooleanFold.prefixStore,sized,compared,prepared,w.injective.eq_iff,a,b,c] using
      empty i (by simp [rawScratch,member])
  obtain ⟨formulaTime,formulaBound,formulaRun⟩ := formulaRoutine_executes extra w raw.2 bits suffix tail marked
    ((accepted && sizeOk) && raw.1.all id)
    (by simp [marked,BooleanFold.prefixStore,w.injective.eq_iff,rest])
    (by simp [marked,BooleanFold.prefixStore,sized,compared,prepared,w.injective.eq_iff,witness])
    (by simp [marked,BooleanFold.prefixStore]) markedEmpty
  have valueEq : ((((accepted && sizeOk) && raw.1.all id) && formulaRange bits raw.2) && formulaValue bits raw.2)=
      (accepted && checkRaw raw bits) := by
    rw [←rawVoteCheck_eq]
    simp only [rawVoteCheck,sizeOk,Bool.and_assoc,Bool.and_left_comm]
  have restored : Function.update (Function.update marked (w 0) suffix)
      (w 1) (((((accepted && sizeOk) && raw.1.all id) && formulaRange bits raw.2) && formulaValue bits raw.2)::tail)=
      Function.update (Function.update store (w 0) suffix) (w 1) ((accepted && checkRaw raw bits)::tail) := by
    rw [valueEq]
    funext r
    by_cases a : r=w 0
    · subst r;simp [w.injective.eq_iff]
    · by_cases b : r=w 1
      · subst r;simp
      · by_cases c : r=w 25
        · subst r;simp [marked,BooleanFold.prefixStore,w.injective.eq_iff,empty,rawScratch]
        · simp [marked,BooleanFold.prefixStore,sized,compared,prepared,a,b,c]
  rw [restored] at formulaRun
  have combined := headerPrepared.sequence (compareRun.sequence (combining.sequence (markersRun.sequence formulaRun)))
  refine ⟨headerTime+1+(Compare.preservingLengthEqualityCost bits (List.replicate raw.1.length true)+1+
    (3+1+(5*raw.1.length+1+1+formulaTime))),?_,combined⟩
  have sourceLength : raw.1.length+rest.length≤(store (w 0)).length := by
    rw [source]
    change _≤((Encoding.natural.encode raw.1.length++Encoding.sequence Encoding.boolean raw.1)++
      (Encoding.list (Encoding.list (Encoding.product Encoding.natural Encoding.boolean))).encode raw.2++suffix).length
    rw [sequence_boolean]
    dsimp [rest]
    simp only [List.length_append]
    omega
  have formulaBound' : formulaTime≤4000*(rest.length+bits.length+1)^5 := by
    simpa [marked,BooleanFold.prefixStore,w.injective.eq_iff] using formulaBound
  have formulaBig : formulaTime≤4000*((store (w 0)).length+bits.length+1)^5 :=
    formulaBound'.trans (Nat.mul_le_mul_left 4000 (Nat.pow_le_pow_left (by omega) 5))
  change headerTime≤1820*((store (w 0)).length+1)^3 at headerBound
  have headerBig : headerTime≤1820*((store (w 0)).length+bits.length+1)^5 := by
    have powered : ((store (w 0)).length+1)^3≤((store (w 0)).length+bits.length+1)^5 := by
      calc
        _≤((store (w 0)).length+bits.length+1)^3 := Nat.pow_le_pow_left (by omega) _
        _≤_ := Nat.pow_le_pow_right (by omega) (by decide)
    exact headerBound.trans (Nat.mul_le_mul_left 1820 powered)
  have comparedBound := Compare.preservingLengthEqualityCost_le bits (List.replicate raw.1.length true)
  simp only [List.length_replicate] at comparedBound
  have linear : (store (w 0)).length+bits.length+1≤((store (w 0)).length+bits.length+1)^5 := Nat.le_self_pow (by decide) _
  omega

end Counting.External.SATVerification
