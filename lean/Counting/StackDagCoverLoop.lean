import Counting.StackDagCoverStep

namespace Counting.StackMachine.DagValidation
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def coverLoopStore (store : Store 33) (accepted : Bool) (tail : List Bool)
    (nodes : List Executable.Node) (start count : Nat) : Store 33:=
  Function.update (Function.update (Function.update (Function.update store 34 []) 26 (start+count).bits)
    24 (start+count+1).bits) 1 ((accepted && coverRange nodes start count)::tail)

theorem coverLoop_executes (store : Store 33) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀ r : Fin 35,r.val<17 → r≠1 → store r=[])
    (extraWork : ∀ r : Fin 35,r∈({21,22,23,27,28,30,31}:Finset (Fin 35)) → store r=[])
    (nodes : List Executable.Node) (start count : Nat) (inside : start+count≤nodes.length)
    (sourceSuffix : List Bool) (source : store 17=Encoding.sequence Encoding.node nodes++sourceSuffix)
    (currentBits : store 26=start.bits) (currentPlus : store 24=(start+1).bits)
    (nodeCount : (store 25).length=nodes.length)
    (bits : List Bool) (counter : store 34=bits) (countEq : bits.length=count) :
    ∃ time ≤ count*(42000*((store 17).length+1)^4+2)+1,
      Executes (forEach 34 coverStep) store time (coverLoopStore store accepted tail nodes start count) := by
  induction count generalizing store accepted start bits with
  | zero=>
    have emptyBits : bits=[]:=List.length_eq_zero_iff.mp countEq
    have empty : store 34=[]:=counter.trans emptyBits
    obtain ⟨ran,halted⟩:=repeat_empty (34:Fin 35) coverStep store empty
    have same : coverLoopStore store accepted tail nodes start 0=store:=by
      funext r
      by_cases r1 : r=1 <;> by_cases r24 : r=24 <;> by_cases r26 : r=26 <;> by_cases r34 : r=34 <;>
        simp [coverLoopStore,coverRange,r1,r24,r26,r34,currentBits,currentPlus,status,empty]
    exact ⟨1,by simp,⟨1,store⟩,ran,halted,same.symm⟩
  | succ count ih=>
    cases bits with
    | nil=>simp at countEq
    | cons bit bits=>
      let consumed:=Function.update store 34 bits
      have consumedWork (r : Fin 35) (small : r.val<17) (ne : r≠1) : consumed r=[]:=by
        have n34 : r≠34:=by intro eq;subst r;norm_num at small
        simp [consumed,n34,work r small ne]
      have consumedExtra (r : Fin 35) (member : r∈({21,22,23,27,28,30,31}:Finset (Fin 35))) : consumed r=[]:=by
        have n34 : r≠34:=by intro eq;subst r;exact (by decide : (34:Fin 35)∉({21,22,23,27,28,30,31}:Finset (Fin 35))) member
        simp [consumed,n34,extraWork r member]
      obtain ⟨bodyTime,bodyBound,finishBody,bodyRun,bodyHalt,bodyStore⟩:=coverStep_executes consumed accepted tail
        (by simp [consumed,status]) consumedWork consumedExtra nodes start (by omega)
        (by simp [consumed,currentBits]) (by simp [consumed,currentPlus]) sourceSuffix
        (by simp [consumed,source]) (by simp [consumed,nodeCount])
      let middle:=coverStepStore consumed accepted tail nodes start
      let nextAccepted:=accepted && !noTableReference start nodes
      have middleWork (r : Fin 35) (small : r.val<17) (ne : r≠1) : middle r=[]:=by
        have n24 : r≠24:=by intro eq;subst r;norm_num at small
        have n26 : r≠26:=by intro eq;subst r;norm_num at small
        simp [middle,coverStepStore,ne,n24,n26,consumedWork r small ne]
      have middleExtra (r : Fin 35) (member : r∈({21,22,23,27,28,30,31}:Finset (Fin 35))) : middle r=[]:=by
        have n1 : r≠1:=by intro eq;subst r;exact (by decide : (1:Fin 35)∉({21,22,23,27,28,30,31}:Finset (Fin 35))) member
        have n24 : r≠24:=by intro eq;subst r;exact (by decide : (24:Fin 35)∉({21,22,23,27,28,30,31}:Finset (Fin 35))) member
        have n26 : r≠26:=by intro eq;subst r;exact (by decide : (26:Fin 35)∉({21,22,23,27,28,30,31}:Finset (Fin 35))) member
        simp [middle,coverStepStore,n1,n24,n26,consumedExtra r member]
      have sourceSame : middle 17=store 17:=by simp [middle,coverStepStore,consumed]
      have nextStatus : middle 1=nextAccepted::tail:=by simp [middle,coverStepStore,nextAccepted]
      have nextIndex : middle 26=(start+1).bits:=by simp [middle,coverStepStore]
      have nextPlus : middle 24=(start+1+1).bits:=by simp [middle,coverStepStore,Nat.add_assoc]
      have nextNodeCount : (middle 25).length=nodes.length:=by simp [middle,coverStepStore,consumed,nodeCount]
      have nextCounter : middle 34=bits:=by simp [middle,coverStepStore,consumed]
      have nextCount : bits.length=count:=by simpa using countEq
      obtain ⟨tailTime,tailBound,finishTail,tailRun,tailHalt,tailStore⟩:=ih middle nextAccepted nextStatus
        middleWork middleExtra (start+1) (by omega) (sourceSame.trans source) nextIndex nextPlus nextNodeCount bits nextCounter nextCount
      have firstRun:=repeat_iteration (34:Fin 35) coverStep store bit bits counter bodyTime finishBody bodyRun bodyHalt
      have final : coverLoopStore middle nextAccepted tail nodes (start+1) count=
          coverLoopStore store accepted tail nodes start (count+1):=by
        funext r
        by_cases r1 : r=1
        · subst r;simp [coverLoopStore,coverRange,nextAccepted,Bool.and_assoc]
        · by_cases r24 : r=24
          · subst r
            change (start+1+count+1).bits=(start+(count+1)+1).bits
            congr 1;omega
          · by_cases r26 : r=26
            · subst r
              change (start+1+count).bits=(start+(count+1)).bits
              congr 1;omega
            · by_cases r34 : r=34
              · subst r;simp [coverLoopStore]
              · simp [coverLoopStore,middle,coverStepStore,consumed,r1,r24,r26,r34]
      refine ⟨bodyTime+2+tailTime,?_,finishTail,?_,tailHalt,tailStore.trans final⟩
      · have inputSame : consumed 17=store 17:=by simp [consumed]
        rw [inputSame] at bodyBound
        rw [sourceSame] at tailBound
        nlinarith
      · rw [Machine.run_add,firstRun,Option.bind_some,bodyStore]
        exact tailRun

end Counting.StackMachine.DagValidation
