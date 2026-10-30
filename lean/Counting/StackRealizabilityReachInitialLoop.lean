import Counting.StackRealizabilityReachIteration
import Counting.StackCompareLengthEquality

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def reachInitialRoles : Fin 6 ↪ Fin 10:=⟨![1,2,3,4,5,6],by decide⟩
def reachInitialItem : Routine 8:=sequence (Compare.preservingLengthEquality 4 reachInitialRoles) (pushBit 2 true)

def reachInitialItemStore (store : Store 8) : Store 8:=
  Function.update (Function.update store 3 (decide ((store 1).length=(store 2).length)::store 3)) 2 (true::store 2)

theorem reachInitialItem_executes (store : Store 8) (e4 : store 4=[]) (e5 : store 5=[]) (e6 : store 6=[])
    (unary : store 2=List.replicate (store 2).length true) :
    ∃ time ≤ 6*((store 1).length+(store 2).length)+13,
      Executes reachInitialItem store time (reachInitialItemStore store):=by
  have comparing:=Compare.preservingLengthEquality_executes 4 reachInitialRoles store e4 e5 e6 unary
  have increment:=pushBit_executes (2:Fin 10) true
    (Function.update store 3 (decide ((store 1).length=(store 2).length)::store 3))
  have same : (Function.update store 3 (decide ((store 1).length=(store 2).length)::store 3)) 2=store 2:=by simp
  rw [same] at increment
  have bound:=Compare.preservingLengthEqualityCost_le (store 1) (store 2)
  exact ⟨_,by change Compare.preservingLengthEqualityCost (store 1) (store 2)+1+1 ≤ _;omega,
    comparing.sequence increment⟩

def reachInitialValues (source : Nat) : Nat → Nat → List Bool
  | _,0=>[]
  | start,count+1=>decide (source=start)::reachInitialValues source (start+1) count

@[simp] theorem reachInitialValues_length (source start count : Nat) :
    (reachInitialValues source start count).length=count:=by
  induction count generalizing start with
  | zero=>rfl
  | succ count ih=>simp [reachInitialValues,ih]

def reachInitialLoopStore (store : Store 8) (counter : List Bool) : Store 8:=
  Function.update (Function.update (Function.update store 8 [])
    3 ((reachInitialValues (store 1).length (store 2).length counter.length).reverse++store 3))
    2 (List.replicate counter.length true++store 2)

theorem reachInitialLoop_executes (store : Store 8) (counter : List Bool) (counted : store 8=counter)
    (e4 : store 4=[]) (e5 : store 5=[]) (e6 : store 6=[])
    (unary : store 2=List.replicate (store 2).length true) :
    ∃ time ≤ counter.length*(6*((store 1).length+(store 2).length+counter.length)+15)+1,
      Executes (forEach 8 reachInitialItem) store time (reachInitialLoopStore store counter):=by
  induction counter generalizing store with
  | nil=>
    obtain ⟨ran,halted⟩:=repeat_empty (8:Fin 10) reachInitialItem store counted
    have final : reachInitialLoopStore store []=store:=by
      funext r
      by_cases r2 : r=2 <;> by_cases r3 : r=3 <;> by_cases r8 : r=8 <;>
        simp [reachInitialLoopStore,reachInitialValues,r2,r3,r8,counted]
    exact ⟨1,by simp,⟨1,store⟩,ran,halted,final.symm⟩
  | cons bit counter ih=>
    let consumed:=Function.update store 8 counter
    obtain ⟨bodyTime,bodyBound,finishBody,bodyRun,bodyHalted,bodyStore⟩:=reachInitialItem_executes consumed
      (by simp [consumed,e4]) (by simp [consumed,e5]) (by simp [consumed,e6]) (by simpa [consumed] using unary)
    let middle:=reachInitialItemStore consumed
    obtain ⟨tailTime,tailBound,finishTail,tailRun,tailHalted,tailStore⟩:=ih middle
      (by simp [middle,reachInitialItemStore,consumed]) (by simp [middle,reachInitialItemStore,consumed,e4])
      (by simp [middle,reachInitialItemStore,consumed,e5]) (by simp [middle,reachInitialItemStore,consumed,e6])
      (by simp only [middle,reachInitialItemStore,Function.update_self,List.length_cons,List.replicate_succ];
          simpa [consumed] using unary)
    have firstRun:=repeat_iteration (8:Fin 10) reachInitialItem store bit counter counted bodyTime finishBody bodyRun bodyHalted
    have final : reachInitialLoopStore middle counter=reachInitialLoopStore store (bit::counter):=by
      funext r
      by_cases r2 : r=2 <;> by_cases r3 : r=3 <;> by_cases r8 : r=8 <;>
        simp [reachInitialLoopStore,middle,reachInitialItemStore,consumed,reachInitialValues,r2,r3,r8,
          List.replicate_succ',List.append_assoc]
    refine ⟨bodyTime+2+tailTime,?_,finishTail,?_,tailHalted,tailStore.trans final⟩
    · have tailSize : (middle 1).length+(middle 2).length+counter.length=
          (store 1).length+(store 2).length+(bit::counter).length:=by
        simp [middle,reachInitialItemStore,consumed];omega
      rw [tailSize] at tailBound
      simp only [consumed,Function.update_of_ne (by decide : (1:Fin 10)≠8),
        Function.update_of_ne (by decide : (2:Fin 10)≠8)] at bodyBound
      let S:=(store 1).length+(store 2).length+(bit::counter).length
      have bodyLimit : bodyTime ≤ 6*S+13:=by dsimp only [S];omega
      change bodyTime+2+tailTime ≤ (bit::counter).length*(6*S+15)+1
      change tailTime ≤ counter.length*(6*S+15)+1 at tailBound
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
    · rw [Machine.run_add,firstRun,Option.bind_some,bodyStore]
      exact tailRun

end Counting.StackMachine.RealizabilityCheck
