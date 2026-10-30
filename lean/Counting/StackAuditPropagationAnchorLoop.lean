import Counting.AuditPropagationAnchorBounds

namespace Counting.StackMachine.AuditPropagation
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000

abbrev anchorLoop : Routine 35 := forEach 32 anchorItem

def anchorLoopStore (store : Store 35) (anchor start : Nat) (remaining : List Executable.Node)
    (values : List Nat) (weights : Array Nat) : Store 35 :=
  Function.update (Function.update (Function.update (Function.update store 32 []) 18
    (List.replicate (start+remaining.length) true)) 36
      (Encoding.sequence Encoding.natural (remainingValues anchor remaining values))) 35
        ((Encoding.array Encoding.natural).encode (assignScan anchor start remaining values weights))

/-- Scan the actual serialized DAG in physical index order. The encoded
weight-array/value-stream potential stays bounded throughout the loop. -/
theorem anchorLoop_executes (store : Store 35) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀ r : Fin 37,r.val<17 → r≠1 → store r=[])
    (e19 : store 19=[]) (e21 : store 21=[]) (e31 : store 31=[])
    (nodes remaining : List Executable.Node) (start : Nat)
    (inside : start+remaining.length ≤ nodes.length)
    (matched : ∀ i (h : i<remaining.length),remaining[i]=nodes[start+i]'(by omega))
    (suffix : List Bool) (input : store 17=Encoding.sequence Encoding.node nodes++suffix)
    (indexCounter : store 18=List.replicate start true)
    (anchor : Nat) (query : store 30=anchor.bits)
    (weights : Array Nat) (sized : weights.size=nodes.length)
    (array : store 35=(Encoding.array Encoding.natural).encode weights)
    (values : List Nat) (source : store 36=Encoding.sequence Encoding.natural values)
    (bits : List Bool) (counter : store 32=bits) (countEq : bits.length=remaining.length) :
    ∃ time ≤ remaining.length*(9000*((store 17).length+(store 35).length+(store 36).length+
        anchor.size+start+remaining.length+1)^4+2)+1,
      Executes anchorLoop store time (anchorLoopStore store anchor start remaining values weights) := by
  induction remaining generalizing store start values weights bits with
  | nil =>
    have bitsEmpty : bits=[] := List.length_eq_zero_iff.mp countEq
    have empty : store 32=[] := counter.trans bitsEmpty
    obtain ⟨ran,halted⟩ := repeat_empty (32:Fin 37) anchorItem store empty
    have finish : anchorLoopStore store anchor start [] values weights=store := by
      simp only [anchorLoopStore,List.length_nil,Nat.add_zero,remainingValues,assignScan]
      rw [←source,←array,←indexCounter,←empty]
      simp only [Function.update_eq_self]
    exact ⟨1,by simp,⟨1,store⟩,ran,halted,finish.symm⟩
  | cons node remaining ih =>
    cases bits with
    | nil => simp at countEq
    | cons bit bits =>
      have indexBound : start<nodes.length := by simp only [List.length_cons] at inside;omega
      let index : Fin nodes.length := ⟨start,indexBound⟩
      have first : node=nodes[index] := by
        exact matched 0 (by simp)
      have restInside : start+1+remaining.length ≤ nodes.length := by
        simp only [List.length_cons] at inside;omega
      have restMatched (i : Nat) (h : i<remaining.length) :
          remaining[i]=nodes[start+1+i]'(by omega) := by
        have found := matched (i+1) (by simp only [List.length_cons];omega)
        simpa only [List.getElem_cons_succ,show start+(i+1)=start+1+i by omega] using found
      let consumed := Function.update store 32 bits
      have consumedWork (r : Fin 37) (small : r.val<17) (different : r≠1) : consumed r=[] := by
        have n32 : r≠32 := by intro same;subst r;norm_num at small
        simp [consumed,n32,work r small different]
      obtain ⟨bodyTime,bodyBound,finishBody,bodyRun,bodyHalt,bodyStore⟩ := anchorItem_executes consumed accepted tail
        (by simp [consumed,status]) consumedWork (by simp [consumed,e19]) (by simp [consumed,e21])
        (by simp [consumed,e31]) nodes index suffix (by simp [consumed,input])
        (by simp [consumed,index,indexCounter]) anchor (by simp [consumed,query]) weights
        (by rw [sized];exact indexBound) (by simp [consumed,array]) values (by simp [consumed,source])
      let nextValues := chosenValues node anchor values
      let nextWeights := chosenWeights node anchor weights start values
      let middle := Function.update (choiceStore consumed node anchor weights start values) 18
        (List.replicate (start+1) true)
      have bodyResult : finishBody.store=middle := by simpa only [index,←first] using bodyStore
      have middleWork (r : Fin 37) (small : r.val<17) (different : r≠1) : middle r=[] := by
        have n18 : r≠18 := by intro same;subst r;norm_num at small
        have n35 : r≠35 := by intro same;subst r;norm_num at small
        have n36 : r≠36 := by intro same;subst r;norm_num at small
        simp [middle,choiceStore,n18,n35,n36,consumedWork r small different]
      have tableSame : middle 17=store 17 := by simp [middle,choiceStore,consumed]
      have weightAt : middle 35=(Encoding.array Encoding.natural).encode nextWeights := by simp [middle,choiceStore,nextWeights]
      have valueAt : middle 36=Encoding.sequence Encoding.natural nextValues := by simp [middle,choiceStore,nextValues]
      obtain ⟨tailTime,tailBound,finishTail,tailRun,tailHalt,tailStore⟩ := ih middle
        (by simp [middle,choiceStore,consumed,status]) middleWork
        (by simp [middle,choiceStore,consumed,e19]) (by simp [middle,choiceStore,consumed,e21])
        (by simp [middle,choiceStore,consumed,e31]) (start+1) restInside restMatched
        (tableSame.trans input) (by simp [middle]) (by simp [middle,choiceStore,consumed,query])
        nextWeights (by simp [nextWeights,sized]) weightAt nextValues valueAt bits
        (by simp [middle,choiceStore,consumed]) (by simpa using countEq)
      have firstRun := repeat_iteration (32:Fin 37) anchorItem store bit bits counter bodyTime finishBody bodyRun bodyHalt
      have final : anchorLoopStore middle anchor (start+1) remaining nextValues nextWeights=
          anchorLoopStore store anchor start (node::remaining) values weights := by
        funext r
        by_cases r18 : r=18 <;> by_cases r32 : r=32 <;> by_cases r35 : r=35 <;> by_cases r36 : r=36 <;>
          simp [anchorLoopStore,middle,choiceStore,consumed,nextValues,nextWeights,
            remainingValues,assignScan_cons,r18,r32,r35,r36,Nat.add_comm,Nat.add_left_comm]
      refine ⟨bodyTime+2+tailTime,?_,finishTail,?_,tailHalt,tailStore.trans final⟩
      · have bodySource : consumed 17=store 17 := by simp [consumed]
        have bodyWeights : consumed 35=store 35 := by simp [consumed]
        have bodyValues : consumed 36=store 36 := by simp [consumed]
        rw [bodySource,bodyWeights,bodyValues] at bodyBound
        rw [tableSame] at tailBound
        have potential : (middle 35).length+(middle 36).length ≤ (store 35).length+(store 36).length := by
          rw [weightAt,valueAt,array,source]
          exact chosen_potential node anchor weights start values
        let size := (store 17).length+(store 35).length+(store 36).length+
          anchor.size+start+(node::remaining).length+1
        have bodyLimit : bodyTime ≤ 9000*size^4 := by
          apply bodyBound.trans
          exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp only [size,index];omega) 4)
        have tailLimit : tailTime ≤ remaining.length*(9000*size^4+2)+1 := by
          apply tailBound.trans
          apply Nat.add_le_add_right
          apply Nat.mul_le_mul_left
          apply Nat.add_le_add_right
          exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp only [size];simp only [List.length_cons];omega) 4)
        change bodyTime+2+tailTime ≤ (node::remaining).length*(9000*size^4+2)+1
        simp only [List.length_cons]
        nlinarith
      · rw [Machine.run_add,firstRun,Option.bind_some,bodyResult]
        exact tailRun

end Counting.StackMachine.AuditPropagation
