import Counting.StackDagDistinctItem

namespace Counting.StackMachine.DagValidation
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

def distinctRange (values : List Executable.Node) (current : Executable.Node) : Nat → Nat → Bool
  | _,0=>true
  | start,count+1=>decide (current≠values[start]?.getD default) && distinctRange values current (start+1) count

def distinctLoopStore (store : Store 33) (accepted : Bool) (tail : List Bool)
    (values : List Executable.Node) (current : Executable.Node) (start count : Nat) : Store 33:=
  Function.update (Function.update (Function.update store 20 []) 18 (List.replicate count true++store 18))
    1 ((accepted && distinctRange values current start count)::tail)

theorem distinctLoop_executes (store : Store 33) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀ r : Fin 35,r.val<17 → r≠1 → store r=[])
    (output : store 19=[])
    (values : List Executable.Node) (start count : Nat) (inside : start+count≤values.length)
    (suffix : List Bool) (source : store 17=Encoding.sequence Encoding.node values++suffix)
    (budget : (store 18).length=start)
    (current : Executable.Node) (currentCode : store 28=Encoding.node.encode current)
    (bits : List Bool) (counter : store 20=bits) (countEq : bits.length=count) :
    ∃ time ≤ count*(10000*((store 17).length+(store 28).length+1)^4+2)+1,
      Executes (forEach 20 distinctItemRoutine) store time (distinctLoopStore store accepted tail values current start count) := by
  induction count generalizing store accepted start bits with
  | zero=>
    have emptyBits : bits=[]:=List.length_eq_zero_iff.mp countEq
    have empty : store 20=[]:=counter.trans emptyBits
    obtain ⟨ran,halted⟩:=repeat_empty (20:Fin 35) distinctItemRoutine store empty
    have same : distinctLoopStore store accepted tail values current start 0=store:=by
      funext r
      by_cases r1 : r=1 <;> by_cases r18 : r=18 <;> by_cases r20 : r=20 <;>
        simp [distinctLoopStore,distinctRange,r1,r18,r20,status,empty]
    exact ⟨1,by simp,⟨1,store⟩,ran,halted,same.symm⟩
  | succ count ih=>
    cases bits with
    | nil=>simp at countEq
    | cons bit bits=>
      have indexBound : start<values.length:=by omega
      let index:Fin values.length:=⟨start,indexBound⟩
      let consumed:=Function.update store 20 bits
      have consumedWork (r : Fin 35) (small : r.val<17) (ne : r≠1) : consumed r=[]:=by
        have n20 : r≠20:=by intro eq;subst r;norm_num at small
        simp [consumed,n20,work r small ne]
      obtain ⟨bodyTime,bodyBound,finishBody,bodyRun,bodyHalt,bodyStore⟩:=distinctItem_executes consumed accepted tail
        (by simp [consumed,status]) consumedWork (by simp [consumed,output]) values index suffix
        (by simp [consumed,source]) (by simp [consumed,index,budget]) current
        (by simp [consumed,currentCode])
      let middle:=distinctItemStore consumed accepted tail values[index] current
      let nextAccepted:=accepted && decide (current≠values[index])
      have middleWork (r : Fin 35) (small : r.val<17) (ne : r≠1) : middle r=[]:=by
        have n18 : r≠18:=by intro eq;subst r;norm_num at small
        simp [middle,distinctItemStore,ne,n18,consumedWork r small ne]
      have sourceSame : middle 17=store 17:=by simp [middle,distinctItemStore,consumed]
      have currentSame : middle 28=store 28:=by simp [middle,distinctItemStore,consumed]
      have nextStatus : middle 1=nextAccepted::tail:=by simp [middle,distinctItemStore,nextAccepted]
      have nextOutput : middle 19=[]:=by simp [middle,distinctItemStore,consumed,output]
      have nextBudget : (middle 18).length=start+1:=by simp [middle,distinctItemStore,consumed,budget]
      have nextCounter : middle 20=bits:=by simp [middle,distinctItemStore,consumed]
      have nextCount : bits.length=count:=by simpa using countEq
      obtain ⟨tailTime,tailBound,finishTail,tailRun,tailHalt,tailStore⟩:=ih middle nextAccepted nextStatus
        middleWork nextOutput (start+1) (by omega) (sourceSame.trans source) nextBudget
        (currentSame.trans currentCode) bits nextCounter nextCount
      have firstRun:=repeat_iteration (20:Fin 35) distinctItemRoutine store bit bits counter bodyTime finishBody bodyRun bodyHalt
      have selected : values[index]=values[start]?.getD default:=by simp [index,indexBound]
      have final : distinctLoopStore middle nextAccepted tail values current (start+1) count=
          distinctLoopStore store accepted tail values current start (count+1):=by
        funext r
        by_cases r1 : r=1
        · subst r;simp [distinctLoopStore,distinctRange,nextAccepted,selected,Bool.and_assoc]
        · by_cases r18 : r=18
          · subst r;simp [distinctLoopStore,middle,distinctItemStore,consumed,List.replicate_succ',List.append_assoc]
          · by_cases r20 : r=20
            · subst r;simp [distinctLoopStore]
            · simp [distinctLoopStore,middle,distinctItemStore,consumed,r1,r18,r20]
      refine ⟨bodyTime+2+tailTime,?_,finishTail,?_,tailHalt,tailStore.trans final⟩
      · have inputSame : consumed 17=store 17:=by simp [consumed]
        have codeSame : consumed 28=store 28:=by simp [consumed]
        rw [inputSame,codeSame] at bodyBound
        rw [sourceSame,currentSame] at tailBound
        nlinarith
      · rw [Machine.run_add,firstRun,Option.bind_some,bodyStore]
        exact tailRun

end Counting.StackMachine.DagValidation
