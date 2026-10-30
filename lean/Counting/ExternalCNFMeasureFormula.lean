import Counting.ExternalCNFMeasureLoop
import Counting.ExternalSATFormula

namespace Counting.External.CNFMachine
open StackMachine StackMachine.Routine StackMachine.EncodingPrograms SATVerification
set_option backward.isDefEq.respectTransparency false

def measureScratch : List (Fin 32) := formulaScratch++[25,30]

def measureFormula (extra : Nat) (w : SATWorkspace extra) : Routine (extra+30) :=
  sequence (readListHeader (extra+15) (satHeaderRoles extra w 0))
    (sequence (ofProgram (ListPrograms.copyProgram (extra+29) (w 23) (w 25) (w 3)))
      (sequence (pushBit (w 27) true) (sequence (measureLoop extra w) (clear (w 27)))))

theorem measureFormula_executes (extra : Nat) (w : SATWorkspace extra)
    (clauses : List (List (Nat×Bool))) (bits suffix tail : List Bool)
    (store : Fin (extra+32) → List Bool) (accepted : Bool)
    (source : store (w 0)=(Encoding.list (Encoding.list (Encoding.product Encoding.natural Encoding.boolean))).encode clauses++suffix)
    (witness : store (w 17)=bits) (status : store (w 1)=accepted::tail)
    (empty : ∀ i∈measureScratch,store (w i)=[]) :
    ∃ time ≤ 7000*((store (w 0)).length+bits.length+1)^5,
      Executes (measureFormula extra w) store time
        (Function.update (Function.update (Function.update (Function.update store (w 25)
          (List.replicate clauses.length true)) (w 31) (List.replicate (rawWidth clauses) true++store (w 31)))
          (w 0) suffix) (w 1) ((accepted && formulaRange bits clauses)::tail)) := by
  have ne (i j : Fin 32) (h : i≠j) : w i≠w j := fun same => h (w.injective same)
  let inputSize := (store (w 0)).length
  let rest := Encoding.sequence (Encoding.list (Encoding.product Encoding.natural Encoding.boolean)) clauses++suffix
  let prepared := Function.update (Function.update store (w 0) rest) (w 23) (List.replicate clauses.length true)
  have headerEmpty (i : Fin 17) (member : i∈({2,3,4,5,8,11,12,13,14,15,16}:Finset (Fin 17))) :
      store ((satHeaderRoles extra w 0) i)=[] := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp [satHeaderRoles,headerPositions,empty,measureScratch,formulaScratch,clauseScratch]
  have positive (clause : List (Nat×Bool)) :
      0<((Encoding.list (Encoding.product Encoding.natural Encoding.boolean)).encode clause).length := by
    rw [Encoding.list_length]
    omega
  obtain ⟨headerTime,headerBound,headerRun⟩ := readListHeader_canonical (extra+15) (satHeaderRoles extra w 0)
    store accepted tail status headerEmpty (Encoding.list (Encoding.product Encoding.natural Encoding.boolean)) positive clauses suffix source
  change Executes (readListHeader (extra+15) (satHeaderRoles extra w 0)) store headerTime prepared at headerRun
  have saving := copy_executes (extra+29) (w 23) (w 25) (w 3)
    (ne 23 25 (by decide)) (ne 23 3 (by decide)) (ne 25 3 (by decide)) prepared
    (by simp [prepared,w.injective.eq_iff,empty,measureScratch,formulaScratch,clauseScratch])
  have preparedCount : prepared (w 23)=List.replicate clauses.length true := by simp [prepared]
  have preparedOutput : prepared (w 25)=[] := by simp [prepared,w.injective.eq_iff,empty,measureScratch]
  rw [preparedCount,preparedOutput,List.append_nil,List.length_replicate] at saving
  let saved := Function.update prepared (w 25) (List.replicate clauses.length true)
  let initialized := Function.update saved (w 27) [true]
  have initializing : Executes (pushBit (w 27) true) saved 1 initialized := by
    simpa only [saved,Function.update_of_ne (ne 27 25 (by decide)),prepared,Function.update_of_ne (ne 27 23 (by decide)),Function.update_of_ne (ne 27 0 (by decide)),
      empty 27 (by simp [measureScratch,formulaScratch]),initialized] using pushBit_executes (w 27) true saved
  have initSource : initialized (w 0)=rest := by simp [initialized,saved,prepared,w.injective.eq_iff]
  have restBound : rest.length ≤ inputSize := by
    dsimp [inputSize]
    rw [source]
    change rest.length≤(Encoding.natural.encode clauses.length++Encoding.sequence
      (Encoding.list (Encoding.product Encoding.natural Encoding.boolean)) clauses++suffix).length
    dsimp [rest]
    simp only [List.length_append]
    omega
  have initWitness : initialized (w 17)=bits := by simp [initialized,saved,prepared,w.injective.eq_iff,witness]
  have initCounter : initialized (w 23)=List.replicate clauses.length true := by simp [initialized,saved,prepared,w.injective.eq_iff]
  have initStatus : initialized (w 1)=accepted::tail := by simp [initialized,saved,prepared,w.injective.eq_iff,status]
  have initEmpty (i : Fin 32) (member : i∈clauseScratch++[30]) : initialized (w i)=[] := by
    have a : i≠0 := by intro same;subst i;simp [clauseScratch] at member
    have b : i≠23 := by intro same;subst i;simp [clauseScratch] at member
    have c : i≠27 := by intro same;subst i;simp [clauseScratch] at member
    have d : i≠25 := by intro same;subst i;simp [clauseScratch] at member
    simpa only [initialized,saved,prepared,Function.update_of_ne (ne i 27 c),Function.update_of_ne (ne i 25 d),Function.update_of_ne (ne i 23 b),
      Function.update_of_ne (ne i 0 a)] using empty i (by simp only [measureScratch,formulaScratch,List.mem_append,List.mem_cons] at *; tauto)
  obtain ⟨loopTime,loopBound,loopRun⟩ := measureLoop_executes extra w clauses bits suffix tail [] inputSize
    initialized accepted true initSource (by rw [initSource];exact restBound) initWitness initCounter initStatus
    (by simp [initialized]) initEmpty
  let checked := Function.update (Function.update (Function.update (Function.update (Function.update initialized (w 31)
    (List.replicate (rawWidth clauses) true++initialized (w 31))) (w 23) []) (w 0) suffix)
    (w 1) ((accepted && formulaRange bits clauses)::tail)) (w 27) [formulaValue bits clauses]
  change Executes (measureLoop extra w) initialized loopTime checked at loopRun
  have clearing := clear_executes (w 27) checked
  have finalValue : checked (w 27)=[formulaValue bits clauses] := by simp [checked]
  rw [finalValue] at clearing
  have restored : Function.update checked (w 27) []=
      Function.update (Function.update (Function.update (Function.update store (w 25)
        (List.replicate clauses.length true)) (w 31) (List.replicate (rawWidth clauses) true++store (w 31)))
        (w 0) suffix) (w 1) ((accepted && formulaRange bits clauses)::tail) := by
    funext r
    by_cases a : r=w 27
    · subst r;simp [w.injective.eq_iff,empty,measureScratch,formulaScratch]
    · by_cases b : r=w 23
      · subst r;simp [checked,w.injective.eq_iff,empty,measureScratch,formulaScratch]
      · by_cases c : r=w 0
        · subst r;simp [checked,w.injective.eq_iff]
        · by_cases d : r=w 1
          · subst r;simp [checked,w.injective.eq_iff]
          · by_cases e : r=w 31
            · subst r;simp [checked,initialized,saved,prepared,w.injective.eq_iff]
            · by_cases f : r=w 25
              · subst r;simp [checked,initialized,saved,w.injective.eq_iff]
              · simp [checked,initialized,saved,prepared,a,b,c,d,e,f]
  rw [restored] at clearing
  have combined := headerRun.sequence (saving.sequence (initializing.sequence (loopRun.sequence clearing)))
  refine ⟨headerTime+1+(5*clauses.length+2+1+(1+1+(loopTime+1+2))),?_,combined⟩
  have clauseCount : clauses.length ≤ inputSize := by
    have sequenceBound := VerifiedParser.sequence_count_le positive clauses
    dsimp [rest] at restBound
    simp only [List.length_append] at restBound
    omega
  have headerBig : headerTime≤1820*(inputSize+bits.length+1)^5 := by
    have cubes : (inputSize+1)^3≤(inputSize+bits.length+1)^5 := by
      calc
        _≤(inputSize+bits.length+1)^3 := Nat.pow_le_pow_left (by omega) _
        _≤_ := Nat.pow_le_pow_right (by omega) (by decide)
    exact headerBound.trans (Nat.mul_le_mul_left 1820 cubes)
  have loopProduct := Nat.mul_le_mul_right (4100*(inputSize+bits.length+1)^4+2) clauseCount
  have fifth : (inputSize+bits.length+1)^5=(inputSize+bits.length+1)^4*(inputSize+bits.length+1) := pow_succ _ _
  have linear : inputSize+bits.length+1≤(inputSize+bits.length+1)^5 := Nat.le_self_pow (by decide) _
  change _≤7000*(inputSize+bits.length+1)^5
  nlinarith

end Counting.External.CNFMachine
