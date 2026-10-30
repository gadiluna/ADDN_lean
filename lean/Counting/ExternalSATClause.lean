import Counting.ExternalSATClauseLoop
import Counting.ExternalSATHeader

namespace Counting.External.SATVerification
open StackMachine StackMachine.Routine StackMachine.EncodingPrograms
set_option backward.isDefEq.respectTransparency false

def clauseRoutine (extra : Nat) (w : SATWorkspace extra) : Routine (extra+30) :=
  sequence (readListHeader (extra+15) (satHeaderRoles extra w 1))
    (sequence (pushBit (w 20) false)
      (sequence (clauseLoop extra w) (BooleanFold.single .conjunction (w 20) (w 27))))

theorem clauseRoutine_executes (extra : Nat) (w : SATWorkspace extra)
    (literals : List (Nat×Bool)) (bits suffix tail valueTail : List Bool)
    (store : Fin (extra+32) → List Bool) (accepted value : Bool)
    (source : store (w 0)=(Encoding.list (Encoding.product Encoding.natural Encoding.boolean)).encode literals++suffix)
    (witness : store (w 17)=bits) (status : store (w 1)=accepted::tail)
    (formula : store (w 27)=value::valueTail)
    (empty : ∀ i∈clauseScratch,store (w i)=[]) :
    ∃ time ≤ 2100*((store (w 0)).length+bits.length+1)^4,
      Executes (clauseRoutine extra w) store time
        (Function.update (Function.update (Function.update store (w 0) suffix)
          (w 1) ((accepted && clauseRange bits literals)::tail))
          (w 27) ((value && clauseValue bits literals)::valueTail)) := by
  have ne (i j : Fin 32) (h : i≠j) : w i≠w j := fun same => h (w.injective same)
  let inputSize := (store (w 0)).length
  let rest := Encoding.sequence (Encoding.product Encoding.natural Encoding.boolean) literals++suffix
  let prepared := Function.update (Function.update store (w 0) rest) (w 24) (List.replicate literals.length true)
  have headerEmpty (i : Fin 17) (member : i∈({2,3,4,5,8,11,12,13,14,15,16}:Finset (Fin 17))) :
      store ((satHeaderRoles extra w 1) i)=[] := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp [satHeaderRoles,headerPositions,empty,clauseScratch]
  have positive (literal : Nat×Bool) : 0<((Encoding.product Encoding.natural Encoding.boolean).encode literal).length := by
    simp [Encoding.product,Encoding.boolean]
  obtain ⟨headerTime,headerBound,headerRun⟩ := readListHeader_canonical (extra+15) (satHeaderRoles extra w 1)
    store accepted tail status headerEmpty (Encoding.product Encoding.natural Encoding.boolean) positive literals suffix source
  change Executes (readListHeader (extra+15) (satHeaderRoles extra w 1)) store headerTime prepared at headerRun
  let initialized := Function.update prepared (w 20) [false]
  have initializing : Executes (pushBit (w 20) false) prepared 1 initialized := by
    simpa only [prepared,Function.update_of_ne (ne 20 24 (by decide)),Function.update_of_ne (ne 20 0 (by decide)),
      empty 20 (by simp [clauseScratch]),initialized] using pushBit_executes (w 20) false prepared
  have initSource : initialized (w 0)=rest := by simp [initialized,prepared,w.injective.eq_iff]
  have restBound : rest.length ≤ inputSize := by
    dsimp [inputSize]
    rw [source]
    change rest.length ≤ (Encoding.natural.encode literals.length++Encoding.sequence
      (Encoding.product Encoding.natural Encoding.boolean) literals++suffix).length
    dsimp [rest]
    simp only [List.length_append]
    omega
  have initWitness : initialized (w 17)=bits := by simp [initialized,prepared,w.injective.eq_iff,witness]
  have initCounter : initialized (w 24)=List.replicate literals.length true := by simp [initialized,prepared,w.injective.eq_iff]
  have initStatus : initialized (w 1)=accepted::tail := by simp [initialized,prepared,w.injective.eq_iff,status]
  have initEmpty (i : Fin 32) (member : i∈literalScratch) : initialized (w i)=[] := by
    have a : i≠0 := by intro same;subst i;simp [literalScratch] at member
    have b : i≠24 := by intro same;subst i;simp [literalScratch] at member
    have c : i≠20 := by intro same;subst i;simp [literalScratch] at member
    simpa only [initialized,prepared,Function.update_of_ne (ne i 20 c),Function.update_of_ne (ne i 24 b),
      Function.update_of_ne (ne i 0 a)] using empty i (literalScratch_subset i member)
  obtain ⟨loopTime,loopBound,loopRun⟩ := clauseLoop_executes extra w literals bits suffix tail [] inputSize
    initialized accepted false initSource (by rw [initSource];exact restBound) initWitness initCounter initStatus
    (by simp [initialized]) initEmpty
  let checked := Function.update (Function.update (Function.update (Function.update initialized (w 24) []) (w 0) suffix)
    (w 1) ((accepted && clauseRange bits literals)::tail)) (w 20) [clauseValue bits literals]
  change Executes (clauseLoop extra w) initialized loopTime checked at loopRun
  have combining := BooleanFold.single_executes .conjunction (w 20) (w 27) (ne 20 27 (by decide)) checked
    (clauseValue bits literals) value [] valueTail (by simp [checked])
    (by simp [checked,initialized,prepared,w.injective.eq_iff,formula])
  have restored : BooleanFold.updated (w 20) (w 27) checked [] (value && clauseValue bits literals) valueTail=
      Function.update (Function.update (Function.update store (w 0) suffix)
        (w 1) ((accepted && clauseRange bits literals)::tail)) (w 27) ((value && clauseValue bits literals)::valueTail) := by
    funext r
    by_cases a : r=w 20
    · subst r;simp [BooleanFold.updated,w.injective.eq_iff,empty,clauseScratch]
    · by_cases b : r=w 24
      · subst r;simp [BooleanFold.updated,checked,w.injective.eq_iff,empty,clauseScratch]
      · by_cases c : r=w 0
        · subst r;simp [BooleanFold.updated,checked,w.injective.eq_iff]
        · by_cases d : r=w 1
          · subst r;simp [BooleanFold.updated,checked,w.injective.eq_iff]
          · simp [BooleanFold.updated,checked,initialized,prepared,Function.update_apply,a,b,c,d]
  change Executes _ checked 3 (BooleanFold.updated (w 20) (w 27) checked []
    (value && clauseValue bits literals) valueTail) at combining
  rw [restored] at combining
  have combined := headerRun.sequence (initializing.sequence (loopRun.sequence combining))
  refine ⟨headerTime+1+(1+1+(loopTime+1+3)),?_,combined⟩
  have literalCount : literals.length ≤ inputSize := by
    have sequenceBound := VerifiedParser.sequence_count_le positive literals
    dsimp [rest] at restBound
    simp only [List.length_append] at restBound
    omega
  have headerBig : headerTime≤1820*(inputSize+bits.length+1)^4 := by
    have cubes : (inputSize+1)^3≤(inputSize+bits.length+1)^4 := by
      calc
        _≤(inputSize+bits.length+1)^3 := Nat.pow_le_pow_left (by omega) _
        _≤_ := Nat.pow_le_pow_right (by omega) (by decide)
    exact headerBound.trans (Nat.mul_le_mul_left 1820 cubes)
  have loopProduct := Nat.mul_le_mul_right (200*(inputSize+bits.length+1)^3+2) literalCount
  have fourth : (inputSize+bits.length+1)^4=(inputSize+bits.length+1)^3*(inputSize+bits.length+1) := pow_succ _ _
  have linear : inputSize+bits.length+1≤(inputSize+bits.length+1)^4 := Nat.le_self_pow (by decide) _
  change _≤2100*(inputSize+bits.length+1)^4
  nlinarith

end Counting.External.SATVerification
