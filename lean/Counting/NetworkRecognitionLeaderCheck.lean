import Counting.NetworkRecognitionLeaderHeader
import Counting.StackDagEmptyGuard
import Counting.StackEncodingGuards

namespace Counting.StackMachine.NetworkRecognition
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

def nonemptyGuard {registers:Nat} (source flag:Fin (registers+2)) : Routine registers :=
  sequence (DagValidation.emptyFlag source flag)
    (sequence (negateFlag registers flag) (ofProgram (combineFlagsProgram registers flag)))

theorem nonemptyGuard_executes {registers:Nat} (store:Store registers) (source flag:Fin (registers+2))
    (accepted:Bool) (tail:List Bool) (status:store flag=accepted::tail) :
    ∃time ≤ 10, Executes (nonemptyGuard source flag) store time
      (Function.update store flag ((accepted && !decide (store source=[]))::tail)) := by
  have checking:=DagValidation.emptyFlag_executes source flag store
  rw [status] at checking
  let flagged:=Function.update store flag (decide (store source=[])::accepted::tail)
  have negating:=negateFlag_executes registers flag flagged (decide (store source=[])) (accepted::tail) (by simp [flagged])
  let inverted:=Function.update flagged flag ((!decide (store source=[]))::accepted::tail)
  have combining:=combineFlags_executes registers flag inverted accepted (!decide (store source=[])) tail (by simp [inverted])
  simp only [inverted,flagged,Function.update_idem] at combining
  simp only [flagged,Function.update_idem] at negating
  have small:DagValidation.emptyFlagCost (store source)≤3:=by unfold DagValidation.emptyFlagCost;split_ifs <;> omega
  exact ⟨_,by omega,checking.sequence (negating.sequence combining)⟩

def leaderCheck : Routine 19 := sequence leaderPrefix
  (sequence (nonemptyGuard 0 1) (sequence (nonemptyGuard 20 1) (sequence (clear 2) (clear 20))))

def leadersAccepted (values:List Bool) : Bool := decide (0<values.length) && decide (0<values.count true)

def leaderCheckStore (store:Store 19) (accepted:Bool) (tail:List Bool) (values suffix:List Bool) : Store 19 :=
  Function.update (Function.update (Function.update store 17 suffix) 0 (List.replicate values.length true))
    1 ((accepted && leadersAccepted values)::tail)

theorem leaderCheck_executes (store:Store 19) (accepted:Bool) (tail:List Bool)
    (status:store 1=accepted::tail) (work:∀r:Fin 21,r.val<17 → r≠1 → store r=[])
    (e18:store 18=[]) (e19:store 19=[]) (e20:store 20=[])
    (values suffix:List Bool) (input:store 17=(Encoding.list Encoding.boolean).encode values++suffix) :
    ∃time ≤ 2000*((store 17).length+1)^3,
      Executes leaderCheck store time (leaderCheckStore store accepted tail values suffix) := by
  obtain ⟨headerTime,headerBound,headerRun⟩:=leaderPrefix_executes store accepted tail status work e18 e19 e20 values suffix input
  let parsed:=leaderPrefixStore store values suffix
  obtain ⟨firstTime,firstBound,firstRun⟩:=nonemptyGuard_executes parsed 0 1 accepted tail
    (by simp [parsed,leaderPrefixStore,status])
  have npos:(!decide (parsed 0=[]))=decide (0<values.length):=by
    simp [parsed,leaderPrefixStore,Nat.pos_iff_ne_zero]
  rw [npos] at firstRun
  let first:=Function.update parsed 1 ((accepted && decide (0<values.length))::tail)
  obtain ⟨secondTime,secondBound,secondRun⟩:=nonemptyGuard_executes first 20 1
    (accepted && decide (0<values.length)) tail (by simp [first])
  have lpos:(!decide (first 20=[]))=decide (0<values.count true):=by
    simp [first,parsed,leaderPrefixStore,Nat.pos_iff_ne_zero]
  rw [lpos] at secondRun
  let second:=Function.update first 1 (((accepted && decide (0<values.length)) && decide (0<values.count true))::tail)
  have clearLeaders:=clear_executes (2:Fin 21) second
  rw [show second 2=values by simp [second,first,parsed,leaderPrefixStore]] at clearLeaders
  let cleared:=Function.update second 2 []
  have clearCount:=clear_executes (20:Fin 21) cleared
  rw [show cleared 20=List.replicate (values.count true) true by simp [cleared,second,first,parsed,leaderPrefixStore],
    List.length_replicate] at clearCount
  have final:Function.update cleared 20 []=leaderCheckStore store accepted tail values suffix:=by
    funext r
    fin_cases r <;> simp [cleared,second,first,parsed,leaderPrefixStore,leaderCheckStore,leadersAccepted,
      Bool.and_assoc,work,e20]
  rw [final] at clearCount
  have countBound:values.length ≤ (store 17).length:=by
    rw [input]
    change values.length ≤ ((Encoding.natural.encode values.length++Encoding.sequence Encoding.boolean values)++suffix).length
    rw [boolean_sequence]
    simp only [List.length_append];omega
  have leaders:=List.count_le_length (a:=true) (l:=values)
  have linear:(store 17).length+1 ≤ ((store 17).length+1)^3:=Nat.le_self_pow (by decide) _
  exact ⟨_,by omega,headerRun.sequence (firstRun.sequence (secondRun.sequence (clearLeaders.sequence clearCount)))⟩

end Counting.StackMachine.NetworkRecognition
