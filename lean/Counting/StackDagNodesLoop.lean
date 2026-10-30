import Counting.StackDagNodeStep

/-! A bounded physical loop checking every requested node, preserving the
DAG source and accumulating the exact executable semantic predicate. -/
namespace Counting.StackMachine.DagValidation
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

def nodeRangeCheck (values : List Executable.Node) : Nat → Nat → Bool
  | _,0=>true
  | start,count+1=>nodeCondition values start (values[start]?.getD default) && nodeRangeCheck values (start+1) count

def nodesLoopStore (store : Store 33) (accepted : Bool) (tail : List Bool)
    (values : List Executable.Node) (start count : Nat) : Store 33:=
  Function.update (Function.update (Function.update (Function.update store 27 []) 24 (start+count).bits)
    29 (List.replicate count true++store 29)) 1 ((accepted && nodeRangeCheck values start count)::tail)

theorem nodesLoop_executes (store : Store 33) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀ r : Fin 35,r.val<17 → r≠1 → store r=[])
    (extraWork : ∀ r : Fin 35,r∈({18,19,20,21,22,23,25,26,28,30,31,32,33,34}:Finset (Fin 35)) → store r=[])
    (values : List Executable.Node) (start count : Nat) (inside : start+count≤values.length)
    (sourceSuffix : List Bool) (source : store 17=Encoding.sequence Encoding.node values++sourceSuffix)
    (currentBits : store 24=start.bits) (budget : (store 29).length=start)
    (bits : List Bool) (counter : store 27=bits) (countEq : bits.length=count) :
    ∃ time ≤ count*(220000100*((store 17).length+1)^5+2)+1,
      Executes (forEach 27 nodeStepRoutine) store time (nodesLoopStore store accepted tail values start count) := by
  induction count generalizing store accepted start bits with
  | zero=>
    have emptyBits : bits=[]:=List.length_eq_zero_iff.mp countEq
    have empty : store 27=[]:=counter.trans emptyBits
    obtain ⟨ran,halted⟩:=repeat_empty (27:Fin 35) nodeStepRoutine store empty
    have same : nodesLoopStore store accepted tail values start 0=store:=by
      funext r
      by_cases r1 : r=1 <;> by_cases r24 : r=24 <;> by_cases r27 : r=27 <;> by_cases r29 : r=29 <;>
        simp [nodesLoopStore,nodeRangeCheck,r1,r24,r27,r29,currentBits,status,empty]
    exact ⟨1,by simp,⟨1,store⟩,ran,halted,same.symm⟩
  | succ count ih=>
    cases bits with
    | nil=>simp at countEq
    | cons bit bits=>
      have indexBound : start<values.length:=by omega
      let index:Fin values.length:=⟨start,indexBound⟩
      let consumed:=Function.update store 27 bits
      have consumedWork (r : Fin 35) (small : r.val<17) (ne : r≠1) : consumed r=[]:=by
        have n27 : r≠27:=by intro eq;subst r;norm_num at small
        simp [consumed,n27,work r small ne]
      have consumedExtra (r : Fin 35) (member : r∈({18,19,20,21,22,23,25,26,28,30,31,32,33,34}:Finset (Fin 35))) : consumed r=[]:=by
        have n27 : r≠27:=by
          intro eq;subst r
          exact (by decide : (27:Fin 35)∉({18,19,20,21,22,23,25,26,28,30,31,32,33,34}:Finset (Fin 35))) member
        simp [consumed,n27,extraWork r member]
      obtain ⟨bodyTime,bodyBound,finishBody,bodyRun,bodyHalt,bodyStore⟩:=nodeStep_executes consumed accepted tail
        (by simp [consumed,status]) consumedWork consumedExtra values index sourceSuffix
        (by simp [consumed,source]) (by simp [consumed,index,currentBits]) (by simp [consumed,index,budget])
      let middle:=nodeStepStore consumed accepted tail values index
      let nextAccepted:=accepted && nodeCondition values start values[index]
      have middleWork (r : Fin 35) (small : r.val<17) (ne : r≠1) : middle r=[]:=by
        have n24 : r≠24:=by intro eq;subst r;norm_num at small
        have n29 : r≠29:=by intro eq;subst r;norm_num at small
        simp [middle,nodeStepStore,ne,n24,n29,consumedWork r small ne]
      have middleExtra (r : Fin 35) (member : r∈({18,19,20,21,22,23,25,26,28,30,31,32,33,34}:Finset (Fin 35))) : middle r=[]:=by
        have n1 : r≠1:=by intro eq;subst r;exact (by decide : (1:Fin 35)∉({18,19,20,21,22,23,25,26,28,30,31,32,33,34}:Finset (Fin 35))) member
        have n24 : r≠24:=by intro eq;subst r;exact (by decide : (24:Fin 35)∉({18,19,20,21,22,23,25,26,28,30,31,32,33,34}:Finset (Fin 35))) member
        have n29 : r≠29:=by intro eq;subst r;exact (by decide : (29:Fin 35)∉({18,19,20,21,22,23,25,26,28,30,31,32,33,34}:Finset (Fin 35))) member
        simp [middle,nodeStepStore,n1,n24,n29,consumedExtra r member]
      have sourceSame : middle 17=store 17:=by simp [middle,nodeStepStore,consumed]
      have nextStatus : middle 1=nextAccepted::tail:=by simp [middle,nodeStepStore,nextAccepted,index]
      have nextIndex : middle 24=(start+1).bits:=by simp [middle,nodeStepStore,index]
      have nextBudget : (middle 29).length=start+1:=by simp [middle,nodeStepStore,consumed,budget]
      have nextCounter : middle 27=bits:=by simp [middle,nodeStepStore,consumed]
      have nextCount : bits.length=count:=by simpa using countEq
      obtain ⟨tailTime,tailBound,finishTail,tailRun,tailHalt,tailStore⟩:=ih middle nextAccepted nextStatus
        middleWork middleExtra (start+1) (by omega) (sourceSame.trans source) nextIndex nextBudget bits nextCounter nextCount
      have firstRun:=repeat_iteration (27:Fin 35) nodeStepRoutine store bit bits counter bodyTime finishBody bodyRun bodyHalt
      have selected : values[index]=values[start]?.getD default:=by simp [index,indexBound]
      have final : nodesLoopStore middle nextAccepted tail values (start+1) count=
          nodesLoopStore store accepted tail values start (count+1):=by
        funext r
        by_cases r1 : r=1
        · subst r;simp [nodesLoopStore,nodeRangeCheck,nextAccepted,selected,Bool.and_assoc]
        · by_cases r24 : r=24
          · subst r
            change (start+1+count).bits=(start+(count+1)).bits
            congr 1; omega
          · by_cases r27 : r=27
            · subst r;simp [nodesLoopStore]
            · by_cases r29 : r=29
              · subst r;simp [nodesLoopStore,middle,nodeStepStore,consumed,List.replicate_succ',List.append_assoc]
              · simp [nodesLoopStore,middle,nodeStepStore,consumed,r1,r24,r27,r29]
      refine ⟨bodyTime+2+tailTime,?_,finishTail,?_,tailHalt,tailStore.trans final⟩
      · have inputSame : consumed 17=store 17:=by simp [consumed]
        rw [inputSame] at bodyBound
        rw [sourceSame] at tailBound
        nlinarith
      · rw [Machine.run_add,firstRun,Option.bind_some,bodyStore]
        exact tailRun

end Counting.StackMachine.DagValidation
