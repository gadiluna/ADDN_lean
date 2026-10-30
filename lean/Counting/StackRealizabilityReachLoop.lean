import Counting.StackRealizabilityReachItem

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- A target accumulates one contribution from each explicit predecessor slot. -/
def reachFold (arcs seen : List Bool) (width : Nat) : Nat → Nat → Nat → Bool → Bool
  | _,_,0,value=>value
  | source,arc,count+1,value=>reachFold arcs seen width (source+1) (arc+width) count
      (value || (RealizabilityVerifier.BitGraph.bitAt seen source && RealizabilityVerifier.BitGraph.bitAt arcs arc))

def reachLoopStore (store : Store 12) (value : Bool) (tail bits : List Bool) : Store 12:=
  Function.update (Function.update (Function.update (Function.update store 13 [])
    5 (reachFold (store 0) (store 1) (store 2).length (store 3).length (store 4).length bits.length value::tail))
    3 (List.replicate bits.length true++store 3))
    4 ((List.replicate bits.length (store 2)).flatten++store 4)

theorem reachLoop_executes (store : Store 12) (value : Bool) (tail bits : List Bool)
    (accumulated : store 5=value::tail) (counted : store 13=bits)
    (e6 : store 6=[]) (e7 : store 7=[])
    (e9 : store 9=[]) (e10 : store 10=[]) (e11 : store 11=[]) (e12 : store 12=[]) :
    ∃ time ≤ bits.length*(60*((store 0).length+(store 1).length+(store 2).length+
        (store 3).length+(store 4).length+1+bits.length*((store 2).length+1))+2)+1,
      Executes (forEach 13 reachItem) store time (reachLoopStore store value tail bits):=by
  induction bits generalizing store value with
  | nil=>
    obtain ⟨ran,halted⟩:=repeat_empty (13:Fin 14) reachItem store counted
    have final : reachLoopStore store value tail []=store:=by
      funext r
      by_cases r3 : r=3 <;> by_cases r4 : r=4 <;> by_cases r5 : r=5 <;> by_cases r13 : r=13 <;>
        simp [reachLoopStore,reachFold,r3,r4,r5,r13,counted,accumulated]
    exact ⟨1,by simp,⟨1,store⟩,ran,halted,final.symm⟩
  | cons bit bits ih=>
    let consumed:=Function.update store 13 bits
    obtain ⟨bodyTime,bodyBound,finishBody,bodyRun,bodyHalted,bodyStore⟩:=reachItem_executes consumed value tail
      (by simp [consumed,accumulated]) (by simp [consumed,e6]) (by simp [consumed,e7])
      (by simp [consumed,e9]) (by simp [consumed,e10]) (by simp [consumed,e11]) (by simp [consumed,e12])
    let nextValue:=value || reachContribution store
    let middle:=reachItemStore consumed value tail
    obtain ⟨tailTime,tailBound,finishTail,tailRun,tailHalted,tailStore⟩:=ih middle nextValue
      (by simp [middle,reachItemStore,nextValue,reachContribution,consumed])
      (by simp [middle,reachItemStore,consumed])
      (by simp [middle,reachItemStore,consumed,e6]) (by simp [middle,reachItemStore,consumed,e7])
      (by simp [middle,reachItemStore,consumed,e9]) (by simp [middle,reachItemStore,consumed,e10])
      (by simp [middle,reachItemStore,consumed,e11]) (by simp [middle,reachItemStore,consumed,e12])
    have firstRun:=repeat_iteration (13:Fin 14) reachItem store bit bits counted bodyTime finishBody bodyRun bodyHalted
    have final : reachLoopStore middle nextValue tail bits=reachLoopStore store value tail (bit::bits):=by
      funext r
      by_cases r3 : r=3 <;> by_cases r4 : r=4 <;> by_cases r5 : r=5 <;> by_cases r13 : r=13 <;>
        simp [reachLoopStore,middle,reachItemStore,consumed,reachFold,nextValue,reachContribution,
          r3,r4,r5,r13,List.replicate_succ',List.flatten_append,List.append_assoc,Nat.add_comm]
    refine ⟨bodyTime+2+tailTime,?_,finishTail,?_,tailHalted,tailStore.trans final⟩
    · simp only [consumed,Function.update_of_ne (by decide : (0:Fin 14)≠13),
        Function.update_of_ne (by decide : (1:Fin 14)≠13),Function.update_of_ne (by decide : (2:Fin 14)≠13),
        Function.update_of_ne (by decide : (3:Fin 14)≠13),Function.update_of_ne (by decide : (4:Fin 14)≠13)] at bodyBound
      have tailSize : (middle 0).length+(middle 1).length+(middle 2).length+
          (middle 3).length+(middle 4).length+1+bits.length*((middle 2).length+1)=
          (store 0).length+(store 1).length+(store 2).length+(store 3).length+(store 4).length+1+
            (bit::bits).length*((store 2).length+1):=by
        simp [middle,reachItemStore,consumed,List.length_cons,List.length_append,Nat.add_mul]
        omega
      rw [tailSize] at tailBound
      let bound:=(store 0).length+(store 1).length+(store 2).length+(store 3).length+(store 4).length+1+
        (bit::bits).length*((store 2).length+1)
      have bodyLimit : bodyTime ≤ 60*bound:=by apply bodyBound.trans;dsimp only [bound];omega
      change bodyTime+2+tailTime ≤ (bit::bits).length*(60*bound+2)+1
      change tailTime ≤ bits.length*(60*bound+2)+1 at tailBound
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
    · rw [Machine.run_add,firstRun,Option.bind_some,bodyStore]
      exact tailRun

end Counting.StackMachine.RealizabilityCheck
