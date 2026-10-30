import Counting.StackDagDistinctAt

/-! Quadratic duplicate scan of the serialized table. Each inner loop is
bounded by the current node index, and all reads/comparisons are physical
stack instructions. The source table remains unchanged. -/
namespace Counting.StackMachine.DagValidation
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

def distinctAllRange (values : List Executable.Node) : Nat → Nat → Bool
  | _,0=>true
  | start,count+1=>distinctRange values (values[start]?.getD default) 0 start && distinctAllRange values (start+1) count

def distinctAllLoopStore (store : Store 33) (accepted : Bool) (tail : List Bool)
    (values : List Executable.Node) (start count : Nat) : Store 33:=
  Function.update (Function.update (Function.update store 27 []) 29 (List.replicate count true++store 29))
    1 ((accepted && distinctAllRange values start count)::tail)

theorem distinctAllLoop_executes (store : Store 33) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀ r : Fin 35,r.val<17 → r≠1 → store r=[])
    (e18 : store 18=[]) (e19 : store 19=[]) (e20 : store 20=[]) (e28 : store 28=[])
    (values : List Executable.Node) (start count : Nat) (inside : start+count≤values.length)
    (suffix : List Bool) (source : store 17=Encoding.sequence Encoding.node values++suffix)
    (budget : (store 29).length=start)
    (bits : List Bool) (counter : store 27=bits) (countEq : bits.length=count) :
    ∃ time ≤ count*(200000*((store 17).length+1)^5+2)+1,
      Executes (forEach 27 distinctAtRoutine) store time (distinctAllLoopStore store accepted tail values start count) := by
  induction count generalizing store accepted start bits with
  | zero=>
    have emptyBits : bits=[]:=List.length_eq_zero_iff.mp countEq
    have empty : store 27=[]:=counter.trans emptyBits
    obtain ⟨ran,halted⟩:=repeat_empty (27:Fin 35) distinctAtRoutine store empty
    have same : distinctAllLoopStore store accepted tail values start 0=store:=by
      funext r
      by_cases r1 : r=1 <;> by_cases r27 : r=27 <;> by_cases r29 : r=29 <;>
        simp [distinctAllLoopStore,distinctAllRange,r1,r27,r29,status,empty]
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
      obtain ⟨bodyTime,bodyBound,finishBody,bodyRun,bodyHalt,bodyStore⟩:=distinctAt_executes consumed accepted tail
        (by simp [consumed,status]) consumedWork (by simp [consumed,e18]) (by simp [consumed,e19])
        (by simp [consumed,e20]) (by simp [consumed,e28]) values index suffix
        (by simp [consumed,source]) (by simp [consumed,index,budget])
      let middle:=distinctAtStore consumed accepted tail values index
      let nextAccepted:=accepted && distinctRange values values[index] 0 start
      have middleWork (r : Fin 35) (small : r.val<17) (ne : r≠1) : middle r=[]:=by
        have n29 : r≠29:=by intro eq;subst r;norm_num at small
        simp [middle,distinctAtStore,ne,n29,consumedWork r small ne]
      have sourceSame : middle 17=store 17:=by simp [middle,distinctAtStore,consumed]
      have nextStatus : middle 1=nextAccepted::tail:=by simp [middle,distinctAtStore,nextAccepted,index]
      have next18 : middle 18=[]:=by simp [middle,distinctAtStore,consumed,e18]
      have next19 : middle 19=[]:=by simp [middle,distinctAtStore,consumed,e19]
      have next20 : middle 20=[]:=by simp [middle,distinctAtStore,consumed,e20]
      have next28 : middle 28=[]:=by simp [middle,distinctAtStore,consumed,e28]
      have nextBudget : (middle 29).length=start+1:=by simp [middle,distinctAtStore,consumed,budget]
      have nextCounter : middle 27=bits:=by simp [middle,distinctAtStore,consumed]
      have nextCount : bits.length=count:=by simpa using countEq
      obtain ⟨tailTime,tailBound,finishTail,tailRun,tailHalt,tailStore⟩:=ih middle nextAccepted nextStatus
        middleWork next18 next19 next20 next28 (start+1) (by omega) (sourceSame.trans source) nextBudget bits nextCounter nextCount
      have firstRun:=repeat_iteration (27:Fin 35) distinctAtRoutine store bit bits counter bodyTime finishBody bodyRun bodyHalt
      have selected : values[index]=values[start]?.getD default:=by simp [index,indexBound]
      have final : distinctAllLoopStore middle nextAccepted tail values (start+1) count=
          distinctAllLoopStore store accepted tail values start (count+1):=by
        funext r
        by_cases r1 : r=1
        · subst r;simp [distinctAllLoopStore,distinctAllRange,nextAccepted,selected,Bool.and_assoc]
        · by_cases r27 : r=27
          · subst r;simp [distinctAllLoopStore]
          · by_cases r29 : r=29
            · subst r;simp [distinctAllLoopStore,middle,distinctAtStore,consumed,List.replicate_succ',List.append_assoc]
            · simp [distinctAllLoopStore,middle,distinctAtStore,consumed,r1,r27,r29]
      refine ⟨bodyTime+2+tailTime,?_,finishTail,?_,tailHalt,tailStore.trans final⟩
      · have inputSame : consumed 17=store 17:=by simp [consumed]
        rw [inputSame] at bodyBound
        rw [sourceSame] at tailBound
        nlinarith
      · rw [Machine.run_add,firstRun,Option.bind_some,bodyStore]
        exact tailRun

def distinctAllFromCount : Routine 33:=sequence (forEach 27 distinctAtRoutine) (clear 29)

theorem distinctAllFromCount_executes (store : Store 33) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀ r : Fin 35,r.val<17 → r≠1 → store r=[])
    (e18 : store 18=[]) (e19 : store 19=[]) (e20 : store 20=[]) (e28 : store 28=[]) (e29 : store 29=[])
    (values : List Executable.Node) (suffix : List Bool)
    (source : store 17=Encoding.sequence Encoding.node values++suffix)
    (counter : (store 27).length=values.length) :
    ∃ time ≤ 210000*((store 17).length+1)^6,
      Executes distinctAllFromCount store time
        (Function.update (Function.update store 27 []) 1 ((accepted && distinctAllRange values 0 values.length)::tail)) := by
  obtain ⟨loopTime,loopBound,loopRun⟩:=distinctAllLoop_executes store accepted tail status work e18 e19 e20 e28
    values 0 values.length (by omega) suffix source (by simp [e29]) (store 27) rfl counter
  let checked:=distinctAllLoopStore store accepted tail values 0 values.length
  have unary : checked 29=List.replicate values.length true:=by simp [checked,distinctAllLoopStore,e29]
  have clearing:=clear_executes (29:Fin 35) checked
  rw [unary,List.length_replicate] at clearing
  have final : Function.update checked 29 []=
      Function.update (Function.update store 27 []) 1 ((accepted && distinctAllRange values 0 values.length)::tail):=by
    funext r
    by_cases r1 : r=1 <;> by_cases r27 : r=27 <;> by_cases r29 : r=29 <;>
      simp [checked,distinctAllLoopStore,r1,r27,r29,e29]
  rw [final] at clearing
  have count:=node_sequence_count_le values
  have nodesBound : values.length≤(store 17).length:=by rw [source,List.length_append];omega
  let S:=(store 17).length+1
  have positiveS : 1≤S:=by dsimp only [S];omega
  have nodesS : values.length≤S:=by dsimp only [S];omega
  have loopLimit : loopTime≤200000*S^6+2*S+1:=by
    have upper : loopTime≤S*(200000*S^5+2)+1:=loopBound.trans (by gcongr)
    nlinarith [show S*S^5=S^6 by ring]
  have linear : S≤S^6:=Nat.le_self_pow (by decide) _
  have one : 1≤S^6:=Nat.one_le_pow _ _ positiveS
  exact ⟨loopTime+1+(values.length+1),by change _≤210000*S^6;omega,loopRun.sequence clearing⟩

end Counting.StackMachine.DagValidation
