import Counting.StackRealizabilityAccumulate
import Counting.StackDagEmptyGuard

namespace Counting.StackMachine.RealizabilityCheck
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

def initialSumRoles (leader : Bool) : Fin 4 ↪ Fin 26:=
  ⟨![if leader then 21 else 22,24,4,5],by cases leader <;> decide⟩

def sumByLeader : Routine 24:=branchRoutine 3
  (accumulateAt (initialSumRoles true)) (accumulateAt (initialSumRoles false))

def selectedSumStore (store : Store 24) (leader : Bool) (leaders nonleaders value : Nat) : Store 24:=
  Function.update (Function.update (Function.update (Function.update store 3 [])
    21 (leaders+(if leader then value else 0)).bits)
      22 (nonleaders+(if leader then 0 else value)).bits) 24 []

theorem sumByLeader_executes (store : Store 24) (leader : Bool) (leaders nonleaders value : Nat)
    (label : store 3=[leader]) (first : store 21=leaders.bits) (second : store 22=nonleaders.bits)
    (weight : store 24=value.bits) (e4 : store 4=[]) (e5 : store 5=[]) :
    ∃ time ≤ 11*(leaders.size+nonleaders.size+value.size)+21,
      Executes sumByLeader store time (selectedSumStore store leader leaders nonleaders value):=by
  let consumed:=Function.update store 3 []
  obtain ⟨time,bound,ran⟩:=accumulateAt_executes (initialSumRoles leader) consumed
    (by simp [initialSumRoles,consumed,e4]) (by simp [initialSumRoles,consumed,e5])
  have atFirst : consumed (initialSumRoles leader 0)=(if leader then leaders else nonleaders).bits:=by
    cases leader <;> simp [consumed,initialSumRoles,first,second]
  have atSecond : consumed (initialSumRoles leader 1)=value.bits:=by simp [consumed,initialSumRoles,weight]
  rw [atFirst,atSecond,Encoding.bits_length,Encoding.bits_length] at bound
  rw [atFirst,atSecond,Encoding.value_bits,Encoding.value_bits] at ran
  have final : Function.update (Function.update consumed (initialSumRoles leader 0)
      ((if leader then leaders else nonleaders)+value).bits) (initialSumRoles leader 1) []=
      selectedSumStore store leader leaders nonleaders value:=by
    funext r
    by_cases r3 : r=3 <;> by_cases r21 : r=21 <;> by_cases r22 : r=22 <;> by_cases r24 : r=24 <;>
      cases leader <;> simp [consumed,initialSumRoles,selectedSumStore,r3,r21,r22,r24,first,second]
  rw [final] at ran
  refine ⟨1+time,?_,?_⟩
  · cases leader <;> simp only [Bool.false_eq_true,ite_false,ite_true] at bound <;> omega
  · cases leader with
    | false=>exact branch_executes_false (3:Fin 26) _ _ store _ [] time label ran
    | true=>exact branch_executes_true (3:Fin 26) _ _ store _ [] time label ran

def initialSum : Routine 24:=sequence (DagValidation.emptyFlag 0 25)
  (branchRoutine 25 sumByLeader (clear 24))

def initialSumStore (store : Store 24) (level : Nat) (leader : Bool) (leaders nonleaders value : Nat) : Store 24:=
  Function.update (Function.update (Function.update (Function.update store
    3 (if level=0 then [] else [leader]))
    21 (leaders+(if level=0 ∧ leader=true then value else 0)).bits)
    22 (nonleaders+(if level=0 ∧ leader=false then value else 0)).bits) 24 []

theorem initialSum_executes (store : Store 24) (level : Nat) (leader : Bool) (leaders nonleaders value : Nat)
    (levelCode : store 0=level.bits) (label : store 3=[leader])
    (first : store 21=leaders.bits) (second : store 22=nonleaders.bits) (weight : store 24=value.bits)
    (e4 : store 4=[]) (e5 : store 5=[]) (e25 : store 25=[]) :
    ∃ time ≤ 30*(leaders.size+nonleaders.size+value.size+1),
      Executes initialSum store time (initialSumStore store level leader leaders nonleaders value):=by
  have checking:=DagValidation.emptyFlag_executes (0:Fin 26) 25 store
  rw [levelCode,e25] at checking
  by_cases zero : level=0
  · subst level
    simp only [Nat.zero_bits,decide_true,DagValidation.emptyFlagCost,ite_true] at checking
    obtain ⟨time,bound,ran⟩:=sumByLeader_executes store leader leaders nonleaders value label first second weight e4 e5
    let checked:=Function.update store 25 [true]
    have restored : Function.update checked 25 []=store:=by
      simp only [checked,Function.update_idem,←e25,Function.update_eq_self]
    have branch:=branch_executes_true (25:Fin 26) sumByLeader (clear 24) checked _ [] time
      (by simp [checked]) (by rw [restored];exact ran)
    have final : selectedSumStore store leader leaders nonleaders value=
        initialSumStore store 0 leader leaders nonleaders value:=by
      cases leader <;> simp [selectedSumStore,initialSumStore]
    rw [final] at branch
    exact ⟨2+1+(1+time),by omega,checking.sequence branch⟩
  · have nonempty : level.bits≠[]:=by
      intro empty
      have equal:=congrArg Encoding.value empty
      simp only [Encoding.value_bits,Encoding.value] at equal
      exact zero equal
    simp only [nonempty,decide_false,DagValidation.emptyFlagCost,if_false] at checking
    let checked:=Function.update store 25 [false]
    have restored : Function.update checked 25 []=store:=by
      simp only [checked,Function.update_idem,←e25,Function.update_eq_self]
    have clearing:=clear_executes (24:Fin 26) store
    rw [weight,Encoding.bits_length] at clearing
    have branch:=branch_executes_false (25:Fin 26) sumByLeader (clear 24) checked _ [] (value.size+1)
      (by simp [checked]) (by rw [restored];exact clearing)
    have final : Function.update store 24 []=initialSumStore store level leader leaders nonleaders value:=by
      funext r
      by_cases r3 : r=3 <;> by_cases r21 : r=21 <;> by_cases r22 : r=22 <;> by_cases r24 : r=24 <;>
        simp [initialSumStore,zero,label,first,second,r3,r21,r22,r24]
    rw [final] at branch
    exact ⟨3+1+(1+(value.size+1)),by omega,checking.sequence branch⟩

end Counting.StackMachine.RealizabilityCheck
