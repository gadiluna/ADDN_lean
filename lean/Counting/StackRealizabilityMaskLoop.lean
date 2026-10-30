import Counting.StackRealizabilityMaskItem

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

def maskRange (nodes : List Executable.Node) (predicate : Executable.Node → Bool) : Nat → Nat → List Bool
  | _,0=>[]
  | start,count+1=>predicate (nodes[start]?.getD default)::maskRange nodes predicate (start+1) count

@[simp] theorem maskRange_length (nodes : List Executable.Node) (predicate : Executable.Node → Bool)
    (start count : Nat) : (maskRange nodes predicate start count).length=count:=by
  induction count generalizing start with
  | zero=>rfl
  | succ count ih=>simp [maskRange,ih]

def maskLoopStore (store : Store 28) (nodes : List Executable.Node) (old next start count : Nat) : Store 28:=
  Function.update (Function.update (Function.update (Function.update (Function.update store 21 [])
    24 ((maskRange nodes (fun node=>decide (node.level=old)) start count).reverse++store 24))
    25 ((maskRange nodes (fun node=>decide (node.level=next)) start count).reverse++store 25))
    26 ((maskRange nodes (fun node=>decide (0<node.degree)) start count).reverse++store 26))
    18 (List.replicate count true++store 18)

theorem maskLoop_executes (store : Store 28) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀ r : Fin 30,r.val<17 → r≠1 → store r=[])
    (e19 : store 19=[]) (e27 : store 27=[])
    (nodes : List Executable.Node) (start : Nat) (counter : List Bool)
    (inside : start+counter.length ≤ nodes.length)
    (suffix : List Bool) (input : store 17=Encoding.sequence Encoding.node nodes++suffix)
    (indexAt : (store 18).length=start) (counted : store 21=counter)
    (old next : Nat) (oldAt : store 22=old.bits) (nextAt : store 23=next.bits) :
    ∃ time ≤ counter.length*(8000*((store 17).length+old.size+next.size+1)^4+2)+1,
      Executes (forEach 21 maskItem) store time (maskLoopStore store nodes old next start counter.length):=by
  induction counter generalizing store start with
  | nil=>
    obtain ⟨ran,halted⟩:=repeat_empty (21:Fin 30) maskItem store counted
    have final : maskLoopStore store nodes old next start 0=store:=by
      funext r
      by_cases r18 : r=18 <;> by_cases r21 : r=21 <;> by_cases r24 : r=24 <;>
        by_cases r25 : r=25 <;> by_cases r26 : r=26 <;>
          simp [maskLoopStore,maskRange,r18,r21,r24,r25,r26,counted]
    exact ⟨1,by simp,⟨1,store⟩,ran,halted,final.symm⟩
  | cons bit counter ih=>
    have indexBound : start<nodes.length:=by simp only [List.length_cons] at inside;omega
    let index : Fin nodes.length:=⟨start,indexBound⟩
    let consumed:=Function.update store 21 counter
    have consumedWork (r : Fin 30) (small : r.val<17) (different : r≠1) : consumed r=[]:=by
      have n21 : r≠21:=by intro same;subst r;norm_num at small
      simp [consumed,n21,work r small different]
    obtain ⟨bodyTime,bodyBound,finishBody,bodyRun,bodyHalted,bodyStore⟩:=maskItem_executes consumed accepted tail
      (by simp [consumed,status]) consumedWork (by simp [consumed,e19]) (by simp [consumed,e27])
      nodes index suffix (by simp [consumed,input]) (by simp [consumed,index,indexAt])
      old next (by simp [consumed,oldAt]) (by simp [consumed,nextAt])
    let middle:=maskItemStore consumed nodes[index] old next
    have middleWork (r : Fin 30) (small : r.val<17) (different : r≠1) : middle r=[]:=by
      have n18 : r≠18:=by intro same;subst r;norm_num at small
      have n24 : r≠24:=by intro same;subst r;norm_num at small
      have n25 : r≠25:=by intro same;subst r;norm_num at small
      have n26 : r≠26:=by intro same;subst r;norm_num at small
      simp [middle,maskItemStore,maskFieldsStore,n18,n24,n25,n26,consumedWork r small different]
    have sourceSame : middle 17=store 17:=by simp [middle,maskItemStore,maskFieldsStore,consumed]
    obtain ⟨tailTime,tailBound,finishTail,tailRun,tailHalted,tailStore⟩:=ih middle
      (by simp [middle,maskItemStore,maskFieldsStore,consumed,status]) middleWork
      (by simp [middle,maskItemStore,maskFieldsStore,consumed,e19])
      (by simp [middle,maskItemStore,maskFieldsStore,consumed,e27]) (start+1)
      (by simp only [List.length_cons] at inside;omega) (sourceSame.trans input)
      (by simp [middle,maskItemStore,maskFieldsStore,consumed,indexAt])
      (by simp [middle,maskItemStore,maskFieldsStore,consumed])
      (by simp [middle,maskItemStore,maskFieldsStore,consumed,oldAt])
      (by simp [middle,maskItemStore,maskFieldsStore,consumed,nextAt])
    have firstRun:=repeat_iteration (21:Fin 30) maskItem store bit counter counted bodyTime finishBody bodyRun bodyHalted
    have selected : nodes[index]=nodes[start]?.getD default:=by simp [index,indexBound]
    have final : maskLoopStore middle nodes old next (start+1) counter.length=
        maskLoopStore store nodes old next start (bit::counter).length:=by
      funext r
      by_cases r18 : r=18 <;> by_cases r21 : r=21 <;> by_cases r24 : r=24 <;>
        by_cases r25 : r=25 <;> by_cases r26 : r=26 <;>
          simp [maskLoopStore,maskRange,middle,maskItemStore,maskFieldsStore,consumed,selected,
            r18,r21,r24,r25,r26,List.replicate_succ',List.append_assoc]
    refine ⟨bodyTime+2+tailTime,?_,finishTail,?_,tailHalted,tailStore.trans final⟩
    · rw [sourceSame] at tailBound
      have same : consumed 17=store 17:=by simp [consumed]
      rw [same] at bodyBound
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
    · rw [Machine.run_add,firstRun,Option.bind_some,bodyStore]
      exact tailRun

end Counting.StackMachine.RealizabilityCheck
