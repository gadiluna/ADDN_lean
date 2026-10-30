import Counting.StackDagEmptyGuard
import Counting.StackEncodingGuards

namespace Counting.StackMachine.AuditPrefix
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

def positiveLabel (source : Fin 52) : Routine 50 := sequence (DagValidation.emptyFlag source 1)
  (sequence (negateFlag 50 1) (ofProgram (combineFlagsProgram 50 1)))

theorem positiveLabel_executes (source : Fin 52) (store : Store 50) (n : Nat)
    (sourceAt : store source=n.bits) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail) :
    ∃ time ≤ 10,Executes (positiveLabel source) store time
      (Function.update store 1 ((accepted && decide (0<n))::tail)) := by
  have a:=DagValidation.emptyFlag_executes source (1:Fin 52) store
  rw [sourceAt,status] at a
  have zero : (n.bits=[]) ↔ n=0 := by
    constructor
    · intro equal;have value:=congrArg Encoding.value equal;simpa only [Encoding.value_bits,Encoding.value] using value
    · rintro rfl;rfl
  simp only [zero] at a
  let tested:=Function.update store 1 (decide (n=0)::accepted::tail)
  have b:=negateFlag_executes 50 (1:Fin 52) tested (decide (n=0)) (accepted::tail) (by simp [tested])
  have positive : (!decide (n=0))=decide (0<n) := by simp [Nat.pos_iff_ne_zero]
  rw [positive] at b
  let negated:=Function.update store 1 (decide (0<n)::accepted::tail)
  have bResult : Function.update tested 1 (decide (0<n)::accepted::tail)=negated := by simp [tested,negated]
  rw [bResult] at b
  have c:=combineFlags_executes 50 (1:Fin 52) negated accepted (decide (0<n)) tail (by simp [negated])
  have cResult : Function.update negated 1 ((accepted && decide (0<n))::tail)=
      Function.update store 1 ((accepted && decide (0<n))::tail) := by simp [negated]
  rw [cResult] at c
  refine ⟨_,?_,a.sequence (b.sequence c)⟩
  have cost : DagValidation.emptyFlagCost n.bits ≤ 3 := by
    unfold DagValidation.emptyFlagCost;split <;> omega
  omega

def labelCompareRoles : Fin 6 ↪ Fin 52 := ⟨![37,38,1,2,3,4],by decide⟩
abbrev candidateGuard : Routine 50 := sequence (Binary.preservingComparison 46 labelCompareRoles)
  (ofProgram (combineFlagsProgram 50 1))

theorem candidateGuard_executes (store : Store 50) (leaders candidate : Nat)
    (leadersAt : store 37=leaders.bits) (candidateAt : store 38=candidate.bits)
    (e2 : store 2=[]) (e3 : store 3=[]) (e4 : store 4=[])
    (accepted : Bool) (tail : List Bool) (status : store 1=accepted::tail) :
    ∃ time ≤ 7*(leaders.size+candidate.size)+13,
      Executes candidateGuard store time
        (Function.update store 1 ((accepted && decide (leaders≤candidate))::tail)) := by
  have a:=Binary.preservingComparison_executes 46 labelCompareRoles store e2 e3 e4
  change Executes _ store (Binary.preservingCompareCost (store 37) (store 38))
    (Function.update store 1 (Binary.compareBits true (store 37) (store 38)::store 1)) at a
  rw [leadersAt,candidateAt,status] at a
  have value : Binary.compareBits true leaders.bits candidate.bits=decide (leaders≤candidate) := by
    apply Bool.eq_iff_iff.mpr
    simp [Binary.compareBits_le,Encoding.value_bits]
  rw [value] at a
  let checked:=Function.update store 1 (decide (leaders≤candidate)::accepted::tail)
  have b:=combineFlags_executes 50 (1:Fin 52) checked accepted (decide (leaders≤candidate)) tail
    (by simp [checked])
  have final : Function.update checked 1 ((accepted && decide (leaders≤candidate))::tail)=
      Function.update store 1 ((accepted && decide (leaders≤candidate))::tail) := by simp [checked]
  rw [final] at b
  refine ⟨_,?_,a.sequence b⟩
  have cost:=Binary.preservingCompareCost_le leaders.bits candidate.bits
  simp only [Encoding.bits_length] at cost
  omega

abbrev labelGuards : Routine 50 := sequence (positiveLabel 37)
  (sequence candidateGuard (positiveLabel 39))

/-- The opening numerical guards compare binary payloads directly. In
particular a large candidate or last-round label is never expanded. -/
theorem labelGuards_executes (store : Store 50) (leaders candidate last : Nat)
    (leadersAt : store 37=leaders.bits) (candidateAt : store 38=candidate.bits) (lastAt : store 39=last.bits)
    (e2 : store 2=[]) (e3 : store 3=[]) (e4 : store 4=[])
    (accepted : Bool) (tail : List Bool) (status : store 1=accepted::tail) :
    ∃ time ≤ 7*(leaders.size+candidate.size)+35,
      Executes labelGuards store time (Function.update store 1
        ((((accepted && decide (0<leaders)) && decide (leaders≤candidate)) && decide (0<last))::tail)) := by
  obtain ⟨positiveTime,positiveBound,a⟩:=positiveLabel_executes 37 store leaders leadersAt accepted tail status
  let positive:=Function.update store 1 ((accepted && decide (0<leaders))::tail)
  obtain ⟨compareTime,compareBound,b⟩:=candidateGuard_executes positive leaders candidate
    (by simp [positive,leadersAt]) (by simp [positive,candidateAt])
    (by simp [positive,e2]) (by simp [positive,e3]) (by simp [positive,e4])
    (accepted && decide (0<leaders)) tail (by simp [positive])
  let compared:=Function.update store 1 (((accepted && decide (0<leaders)) && decide (leaders≤candidate))::tail)
  have bResult : Function.update positive 1
      (((accepted && decide (0<leaders)) && decide (leaders≤candidate))::tail)=compared := by simp [positive,compared]
  rw [bResult] at b
  obtain ⟨lastTime,lastBound,c⟩:=positiveLabel_executes 39 compared last
    (by simp [compared,lastAt]) ((accepted && decide (0<leaders)) && decide (leaders≤candidate)) tail
    (by simp [compared])
  simp only [compared,Function.update_idem] at c
  exact ⟨_,by omega,a.sequence (b.sequence c)⟩

end Counting.StackMachine.AuditPrefix
