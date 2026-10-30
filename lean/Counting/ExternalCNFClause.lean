import Counting.ExternalCNFClauseLayout
import Counting.ExternalCNFFinish

namespace Counting.External.CNFMachine
open StackMachine StackMachine.Routine SATVerification
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 65536

def clauseFinishPositions : Fin 7 ↪ Fin 52 := ⟨![48,33,32,42,43,44,34],by
  intro i j equal;fin_cases i <;> fin_cases j <;> simp_all⟩
def clauseFinishRoles (extra : Nat) (w : ClauseWorkspace extra) : FinishWorkspace (extra+45) :=
  clauseFinishPositions.trans w

def clauseRows (current width : Nat) (literals : List (Nat×Bool)) : List (List (Nat×Bool)) :=
  gateRows current (current+width) width literals++
    [List.replicate 3 (current,true),List.replicate 3 (current+width,false)]

def generatorClause (extra : Nat) (w : ClauseWorkspace extra) : Routine (extra+50) :=
  sequence (generatorClausePrepare extra w)
    (sequence (gateLoop (extra+6) (clauseLoopRoles extra w)) (finishClause (extra+45) (clauseFinishRoles extra w)))

def clauseResult (extra : Nat) (w : ClauseWorkspace extra) (store : Fin (extra+52) → List Bool)
    (width : Nat) (literals : List (Nat×Bool)) (suffix : List Bool) :=
  Function.update (Function.update (Function.update store (w 0) suffix)
    (w 34) (List.replicate (width+1) true++store (w 34)))
    (w 42) ((Encoding.sequence (Encoding.list literalCodec) (clauseRows (store (w 34)).length width literals)).reverse++store (w 42))

theorem literal_length_le (index : Nat) (sign : Bool) : (literalCodec.encode (index,sign)).length≤2*index+2 := by
  have size : index.size ≤ index := Nat.size_le.mpr Nat.lt_two_pow_self
  simp only [literalCodec,Encoding.product,Encoding.boolean,List.length_append,List.length_singleton,Encoding.natural_length]
  omega

theorem generatorClause_executes (extra : Nat) (w : ClauseWorkspace extra)
    (store : Fin (extra+52) → List Bool) (width limitCode : Nat) (literals : List (Nat×Bool))
    (accepted : Bool) (suffix tail : List Bool)
    (source : store (w 0)=(Encoding.list literalCodec).encode literals++suffix)
    (status : store (w 1)=accepted::tail)
    (widthEq : store (w 47)=List.replicate width true)
    (longEnough : literals.length≤width)
    (empty : ∀ i∈generatorClauseScratch,store (w i)=[])
    (bounded : ∀ j<width,∀ i : Fin 6,
      (literalCodec.encode (gateSource ((store (w 34)).length+j)
        ((literals.drop j).headD ((store (w 34)).length+width,true)) i)).length≤limitCode) :
    ∃ time ≤ 50000*((store (w 0)).length+(store (w 34)).length+width+limitCode+2)^3,
      Executes (generatorClause extra w) store time (clauseResult extra w store width literals suffix) := by
  let current := (store (w 34)).length
  let ready := clausePrepared extra w store literals suffix
  have widthLen : (store (w 47)).length=width := by simp [widthEq]
  obtain ⟨prepareTime,prepareBound,preparing⟩ := generatorClausePrepare_executes extra w store literals accepted suffix tail source status empty
  have readySource : ready (w 0)=Encoding.sequence literalCodec literals++suffix := by simp [ready,clausePrepared,w.injective.eq_iff]
  have readyBound : (ready (w 0)).length≤(store (w 0)).length := by
    rw [readySource,source]
    simp only [Encoding.list,List.length_append]
    omega
  have readyCounter : ready (w 24)=List.replicate literals.length true := by simp [ready,clausePrepared,w.injective.eq_iff]
  have readyIterations : ready (w 45)=List.replicate width true := by simp [ready,clausePrepared,w.injective.eq_iff,widthEq]
  have readyStatus : ready (w 1)=accepted::tail := by simp [ready,clausePrepared,w.injective.eq_iff,status]
  have readyPositive : ready (w 32)=literalCodec.encode (current+width,true) := by simp [ready,clausePrepared,w.injective.eq_iff,widthLen,current]
  have readyNegative : ready (w 33)=literalCodec.encode (current+width,false) := by simp [ready,clausePrepared,widthLen,current]
  have readyCurrent : ready (w 34)=store (w 34) := by simp [ready,clausePrepared,w.injective.eq_iff]
  have readyEmpty (i : Fin 45) (member : i∈stepScratch) : ready (w (Fin.castLE (by decide : 45≤52) i))=[] := by
    simp only [stepScratch,List.mem_cons,List.not_mem_nil] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|h
    all_goals first | contradiction | simp [ready,clausePrepared,w.injective.eq_iff,empty,generatorClauseScratch]
  obtain ⟨loopTime,loopBound,looping⟩ := gateLoop_executes (extra+6) (clauseLoopRoles extra w) width ready literals
    (current+width) (store (w 0)).length limitCode accepted suffix tail readySource readyBound readyCounter readyIterations
    readyStatus readyPositive readyNegative readyEmpty (by
      intro j less i
      change (literalCodec.encode (gateSource ((ready (w 34)).length+j) ((literals.drop j).headD (current+width,true)) i)).length≤limitCode
      rw [readyCurrent]
      exact bounded j less i)
  let looped := loopResult (extra+6) (clauseLoopRoles extra w) ready width literals (current+width) suffix
  have gone : literals.drop width=[] := List.drop_eq_nil_iff.mpr longEnough
  have baseCode : looped (w 48)=literalCodec.encode (current,true) := by
    simp [looped,loopResult,clauseLoopRoles,ready,clausePrepared,w.injective.eq_iff,current]
  have terminalCode : looped (w 33)=literalCodec.encode (current+width,false) := by
    simp [looped,loopResult,clauseLoopRoles,ready,clausePrepared,w.injective.eq_iff,current,widthLen]
  obtain ⟨finishTime,finishBound,finishing⟩ := finishClause_executes (extra+45) (clauseFinishRoles extra w) looped current (current+width)
    baseCode terminalCode
    (by simp [clauseFinishRoles,clauseFinishPositions,looped,loopResult,clauseLoopRoles,ready,clausePrepared,w.injective.eq_iff,empty 43 (by decide)])
    (by simp [clauseFinishRoles,clauseFinishPositions,looped,loopResult,clauseLoopRoles,ready,clausePrepared,w.injective.eq_iff,empty 44 (by decide)])
  have finalStore : finishResult (extra+45) (clauseFinishRoles extra w) looped current (current+width)=clauseResult extra w store width literals suffix := by
    funext r
    by_cases a : r=w 0
    · subst r;simp [finishResult,clauseFinishRoles,clauseFinishPositions,looped,loopResult,clauseLoopRoles,clauseResult,gone,Encoding.sequence,w.injective.eq_iff]
    · by_cases b : r=w 34
      · subst r
        simp [finishResult,clauseFinishRoles,clauseFinishPositions,looped,loopResult,clauseLoopRoles,clauseResult,readyCurrent,List.replicate_succ,w.injective.eq_iff]
      · by_cases c : r=w 42
        · subst r
          simp [finishResult,clauseFinishRoles,clauseFinishPositions,looped,loopResult,clauseLoopRoles,clauseResult,ready,clausePrepared,
            clauseRows,sequence_append,List.reverse_append,List.append_assoc,w.injective.eq_iff,current]
        · by_cases d : r=w 24
          · subst r;simp [finishResult,clauseFinishRoles,clauseFinishPositions,looped,loopResult,clauseLoopRoles,clauseResult,gone,w.injective.eq_iff,empty 24 (by decide)]
          · by_cases e : r=w 45
            · subst r;simp [finishResult,clauseFinishRoles,clauseFinishPositions,looped,loopResult,clauseLoopRoles,clauseResult,w.injective.eq_iff,empty 45 (by decide)]
            · by_cases f : r=w 48
              · subst r;simp [finishResult,clauseFinishRoles,clauseFinishPositions,clauseResult,w.injective.eq_iff,empty 48 (by decide)]
              · by_cases g : r=w 32
                · subst r;simp [finishResult,clauseFinishRoles,clauseFinishPositions,clauseResult,w.injective.eq_iff,empty 32 (by decide)]
                · by_cases h : r=w 33
                  · subst r;simp [finishResult,clauseFinishRoles,clauseFinishPositions,clauseResult,w.injective.eq_iff,empty 33 (by decide)]
                  · simp [finishResult,clauseFinishRoles,clauseFinishPositions,looped,loopResult,clauseLoopRoles,ready,clausePrepared,
                      clauseResult,a,b,c,d,e,f,g,h]
  rw [finalStore] at finishing
  have combined := preparing.sequence (looping.sequence finishing)
  refine ⟨prepareTime+1+(loopTime+1+finishTime),?_,combined⟩
  rw [widthLen] at prepareBound
  have loopEstimate : loopTime≤width*(1000*((store (w 0)).length+(literalCodec.encode (current+width,true)).length+
      (literalCodec.encode (current+width,false)).length+limitCode+current+width+2)^2+2)+1 := by
    change loopTime≤width*(1000*((store (w 0)).length+(ready (w 32)).length+(ready (w 33)).length+limitCode+(ready (w 34)).length+width+2)^2+2)+1 at loopBound
    rw [readyPositive,readyNegative,readyCurrent] at loopBound
    exact loopBound
  have finishEstimate : finishTime≤100*((literalCodec.encode (current,true)).length+
      (literalCodec.encode (current+width,false)).length+(literalCodec.encode (current+width,true)).length+1) := by
    simpa [clauseFinishRoles,clauseFinishPositions,looped,loopResult,clauseLoopRoles,ready,clausePrepared,w.injective.eq_iff,current,widthLen] using finishBound
  let S := (store (w 0)).length+current+width+limitCode+2
  have positiveS : 1≤S := by dsimp [S];omega
  have Ssquare : S≤S^2 := Nat.le_self_pow (by decide : 2≠0) S
  have Scube : S≤S^3 := Nat.le_self_pow (by decide : 3≠0) S
  have posCube : 1≤S^3 := Nat.one_le_pow 3 S positiveS
  have code0 := literal_length_le current true
  have code1 := literal_length_le (current+width) true
  have code2 := literal_length_le (current+width) false
  have preparationLimit : prepareTime≤2000*S^3 := prepareBound.trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp [S,current];omega) 3))
  have inner : (store (w 0)).length+(literalCodec.encode (current+width,true)).length+
      (literalCodec.encode (current+width,false)).length+limitCode+current+width+2≤5*S := by dsimp [S];omega
  have widthBound : width≤S := by dsimp [S];omega
  have loopLimit : loopTime≤25000*S^3+2*S+1 := by
    have factor := Nat.pow_le_pow_left inner 2
    have product := Nat.mul_le_mul widthBound (Nat.add_le_add_right (Nat.mul_le_mul_left 1000 factor) 2)
    calc
      loopTime≤width*(1000*((store (w 0)).length+(literalCodec.encode (current+width,true)).length+
        (literalCodec.encode (current+width,false)).length+limitCode+current+width+2)^2+2)+1 := loopEstimate
      _≤S*(1000*(5*S)^2+2)+1 := Nat.add_le_add_right product 1
      _=25000*S^3+2*S+1 := by ring
  have finishLimit : finishTime≤700*S := by dsimp [S];omega
  change _≤50000*S^3
  nlinarith only [preparationLimit,loopLimit,finishLimit,Scube,posCube]

end Counting.External.CNFMachine
