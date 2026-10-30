import Counting.StackProtocolScheduleSpec
import Counting.StackBinaryComparePreserving
import Counting.StackComparePreserving
import Counting.StackDagEmptyGuard
import Counting.StackEncodingFrameStore
import Counting.StackUnframeCanonical
import Counting.PositiveNaturalsSpec

namespace Counting.StackMachine.ProtocolSchedule
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

def file (input output leaders round candidate last flag : List Bool) : Store 14 := fun r=>
  if r=0 then input else if r=1 then output else if r=8 then leaders else if r=9 then round
  else if r=10 then candidate else if r=11 then last else if r=2 then flag else []

def fields (leaders round candidate last : Nat) (flag : List Bool) : Store 14 :=
  file [] [] leaders.bits round.bits candidate.bits last.bits flag

def inputWord (leaders round : Nat) : List Bool := Encoding.natural.encode leaders++Encoding.natural.encode round
def outputWord (result : Option (Nat×Nat)) : List Bool :=
  (Encoding.optional (Encoding.product Encoding.natural Encoding.natural)).encode result

abbrev parse : Routine 14 := sequence (ofProgram (unframeProgram 13 0 8 15))
  (ofProgram (unframeProgram 13 0 9 15))

theorem parse_executes (leaders round : Nat) :
    Executes parse (inputStore 14 (inputWord leaders round)) (5*leaders.size+5*round.size+5)
      (fields leaders round 0 0 []) := by
  let initial:=file (inputWord leaders round) [] [] [] [] [] []
  have a:=unframe_canonical_executes 13 (0:Fin 16) 8 15 (by decide) (by decide) (by decide)
    initial leaders.bits (Encoding.natural.encode round) rfl rfl
  let first:=file (Encoding.natural.encode round) [] leaders.bits [] [] [] []
  have firstStore : Function.update (Function.update initial 0 (Encoding.natural.encode round)) 8
      (leaders.bits++initial 8)=first := by
    funext r;fin_cases r <;> simp [initial,first,file]
  rw [firstStore] at a
  have b:=unframe_canonical_executes 13 (0:Fin 16) 9 15 (by decide) (by decide) (by decide)
    first round.bits [] (by simp [first,file,Encoding.natural]) rfl
  have final : Function.update (Function.update first 0 []) 9 (round.bits++first 9)=fields leaders round 0 0 [] := by
    funext r;fin_cases r <;> simp [first,file,fields]
  rw [final] at b
  have begin:initial=inputStore 14 (inputWord leaders round) := by
    funext r;fin_cases r <;> simp [initial,file,inputStore]
  rw [begin] at a
  have run:=a.sequence b
  simpa only [Encoding.bits_length,show 5*leaders.size+2+1+(5*round.size+2)=5*leaders.size+5*round.size+5 by omega] using run

def roundRoles : Fin 6 ↪ Fin 16 := ⟨![9,8,2,3,4,5],by decide⟩
def candidateRoles : Fin 6 ↪ Fin 16 := ⟨![10,8,2,3,4,5],by decide⟩
def oneRoles : Fin 6 ↪ Fin 16 := ⟨![8,6,2,3,4,5],by decide⟩

abbrev compareRound : Routine 14 := Binary.preservingComparison 10 roundRoles
abbrev compareCandidate : Routine 14 := Binary.preservingComparison 10 candidateRoles

theorem compare_natural (left right : Nat) :
    Binary.compareBits true left.bits right.bits=decide (left≤ right) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Binary.compareBits_le,Encoding.value_bits,decide_eq_true_eq]

theorem compareRound_executes (leaders round candidate last : Nat) :
    ∃ time≤ 7*(round.size+leaders.size)+9,
      Executes compareRound (fields leaders round candidate last []) time
        (fields leaders round candidate last [decide (round≤ leaders)]) := by
  have run:=Binary.preservingComparison_executes 10 roundRoles (fields leaders round candidate last []) rfl rfl rfl
  change Executes _ _ (Binary.preservingCompareCost round.bits leaders.bits)
    (Function.update (fields leaders round candidate last []) 2 [Binary.compareBits true round.bits leaders.bits]) at run
  rw [compare_natural] at run
  have target:Function.update (fields leaders round candidate last []) 2 [decide (round≤ leaders)]=
      fields leaders round candidate last [decide (round≤ leaders)] := by
    funext r;by_cases flag:r=2 <;> simp [fields,file,flag]
  rw [target] at run
  exact ⟨_,by simpa only [Encoding.bits_length] using Binary.preservingCompareCost_le round.bits leaders.bits,run⟩

theorem compareCandidate_executes (leaders round candidate last : Nat) :
    ∃ time≤ 7*(candidate.size+leaders.size)+9,
      Executes compareCandidate (fields leaders round candidate last []) time
        (fields leaders round candidate last [decide (candidate≤ leaders)]) := by
  have run:=Binary.preservingComparison_executes 10 candidateRoles (fields leaders round candidate last []) rfl rfl rfl
  change Executes _ _ (Binary.preservingCompareCost candidate.bits leaders.bits)
    (Function.update (fields leaders round candidate last []) 2 [Binary.compareBits true candidate.bits leaders.bits]) at run
  rw [compare_natural] at run
  have target:Function.update (fields leaders round candidate last []) 2 [decide (candidate≤ leaders)]=
      fields leaders round candidate last [decide (candidate≤ leaders)] := by
    funext r;by_cases flag:r=2 <;> simp [fields,file,flag]
  rw [target] at run
  exact ⟨_,by simpa only [Encoding.bits_length] using Binary.preservingCompareCost_le candidate.bits leaders.bits,run⟩

end Counting.StackMachine.ProtocolSchedule
