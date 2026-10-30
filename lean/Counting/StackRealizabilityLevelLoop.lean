import Counting.StackRealizabilityLevelSpec

namespace Counting.StackMachine.RealizabilityCheck
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def levelLoopStore (store : Store 25) (nodes : List Executable.Node) (target start total : Nat)
    (values : List Nat) (suffix : List Bool) : Store 25:=
  Function.update (Function.update (Function.update (Function.update store 23 []) 20 suffix)
    21 (total+levelRangeSum nodes target start values).bits)
      18 (List.replicate values.length true++store 18)

theorem levelLoop_executes (store : Store 25) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀ r : Fin 27,r.val<17 → r≠1 → store r=[])
    (e19 : store 19=[]) (e24 : store 24=[]) (e26 : store 26=[])
    (nodes : List Executable.Node) (start : Nat) (values : List Nat) (inside : start+values.length ≤ nodes.length)
    (nodeSuffix : List Bool) (nodeInput : store 17=Encoding.sequence Encoding.node nodes++nodeSuffix)
    (indexCounter : (store 18).length=start)
    (target total : Nat) (level : store 22=target.bits) (e25 : store 25=[])
    (accumulator : store 21=total.bits)
    (suffix : List Bool) (input : store 20=Encoding.sequence Encoding.natural values++suffix)
    (bits : List Bool) (counter : store 23=bits) (countEq : bits.length=values.length) :
    ∃ time ≤ values.length*(8000*((store 17).length+(store 20).length+total.size+
        target.size+1)^4+2)+1,
      Executes (forEach 23 levelItem) store time (levelLoopStore store nodes target start total values suffix):=by
  induction values generalizing store start total bits with
  | nil=>
    have emptyBits : bits=[]:=List.length_eq_zero_iff.mp countEq
    have empty : store 23=[]:=counter.trans emptyBits
    have source : store 20=suffix:=by simpa only [Encoding.sequence,List.nil_append] using input
    obtain ⟨ran,halted⟩:=repeat_empty (23:Fin 27) levelItem store empty
    have final : levelLoopStore store nodes target start total [] suffix=store:=by
      funext r
      by_cases r18 : r=18 <;> by_cases r20 : r=20 <;> by_cases r21 : r=21 <;>
        by_cases r23 : r=23 <;>
        simp [levelLoopStore,levelRangeSum,r18,r20,r21,r23,empty,source,accumulator]
    exact ⟨1,by simp,⟨1,store⟩,ran,halted,final.symm⟩
  | cons value values ih=>
    cases bits with
    | nil=>simp at countEq
    | cons bit bits=>
      have indexBound : start<nodes.length:=by simp only [List.length_cons] at inside;omega
      let index : Fin nodes.length:=⟨start,indexBound⟩
      let consumed:=Function.update store 23 bits
      let remaining:=Encoding.sequence Encoding.natural values++suffix
      have consumedWork (r : Fin 27) (small : r.val<17) (different : r≠1) : consumed r=[]:=by
        have n23 : r≠23:=by intro same;subst r;norm_num at small
        simp [consumed,n23,work r small different]
      have headInput : consumed 20=Encoding.natural.encode value++remaining:=by
        simpa only [consumed,Function.update_of_ne (by decide : (20:Fin 27)≠23),
          Encoding.sequence,List.append_assoc] using input
      obtain ⟨bodyTime,bodyBound,finishBody,bodyRun,bodyHalt,bodyStore⟩:=levelItem_executes consumed accepted tail
        (by simp [consumed,status]) consumedWork (by simp [consumed,e19])
        (by simp [consumed,e24]) (by simp [consumed,e26]) nodes index nodeSuffix
        (by simp [consumed,nodeInput]) (by simp [consumed,index,indexCounter]) target total value
        (by simp [consumed,level]) (by simp [consumed,e25]) (by simp [consumed,accumulator]) remaining headInput
      let middle:=levelItemStore consumed nodes[index] target total value remaining
      let nextTotal:=total+levelContribution nodes[index] target value
      have middleWork (r : Fin 27) (small : r.val<17) (different : r≠1) : middle r=[]:=by
        have n18 : r≠18:=by intro same;subst r;norm_num at small
        have n20 : r≠20:=by intro same;subst r;norm_num at small
        have n21 : r≠21:=by intro same;subst r;norm_num at small
        simp [middle,levelItemStore,n18,n20,n21,consumedWork r small different]
      have sourceSame : middle 17=store 17:=by simp [middle,levelItemStore,consumed]
      obtain ⟨tailTime,tailBound,finishTail,tailRun,tailHalt,tailStore⟩:=ih middle
        (by simp [middle,levelItemStore,consumed,status]) middleWork
        (by simp [middle,levelItemStore,consumed,e19]) (by simp [middle,levelItemStore,consumed,e24])
        (by simp [middle,levelItemStore,consumed,e26]) (start+1) (by simp only [List.length_cons] at inside;omega)
        (sourceSame.trans nodeInput) (by simp [middle,levelItemStore,consumed,indexCounter])
        nextTotal (by simp [middle,levelItemStore,consumed,level])
        (by simp [middle,levelItemStore,consumed,e25]) (by simp [middle,levelItemStore,nextTotal])
        (by simp [middle,levelItemStore,remaining]) bits
        (by simp [middle,levelItemStore,consumed]) (by simpa using countEq)
      have firstRun:=repeat_iteration (23:Fin 27) levelItem store bit bits counter bodyTime finishBody bodyRun bodyHalt
      have selected : nodes[index]=nodes[start]?.getD default:=by simp [index,indexBound]
      have final : levelLoopStore middle nodes target (start+1) nextTotal values suffix=
          levelLoopStore store nodes target start total (value::values) suffix:=by
        funext r
        by_cases r18 : r=18 <;> by_cases r20 : r=20 <;> by_cases r21 : r=21 <;> by_cases r23 : r=23 <;>
          simp [levelLoopStore,levelRangeSum,middle,levelItemStore,consumed,nextTotal,selected,
            r18,r20,r21,r23,Nat.add_assoc,List.replicate_succ',List.append_assoc]
      refine ⟨bodyTime+2+tailTime,?_,finishTail,?_,tailHalt,tailStore.trans final⟩
      · have nodeSame : consumed 17=store 17:=by simp [consumed]
        have weightSame : consumed 20=store 20:=by simp [consumed]
        rw [nodeSame,weightSame] at bodyBound
        rw [sourceSame] at tailBound
        have sourceSize : (middle 20).length+nextTotal.size ≤ (store 20).length+total.size:=by
          have sizeBound:=level_total_size nodes[index] target total value
          rw [input]
          simp only [middle,levelItemStore,Function.update_of_ne (by decide : (20:Fin 27)≠18),
            Function.update_of_ne (by decide : (20:Fin 27)≠21),Function.update_self]
          simp only [remaining,Encoding.sequence,List.length_append,Encoding.natural_length]
          dsimp only [nextTotal]
          omega
        have tailLimit : tailTime ≤ values.length*(8000*
            ((store 17).length+(store 20).length+total.size+target.size+1)^4+2)+1:=by
          apply tailBound.trans
          have totalSize : (store 17).length+(middle 20).length+nextTotal.size+target.size+1 ≤
              (store 17).length+(store 20).length+total.size+target.size+1:=by omega
          exact Nat.add_le_add_right (Nat.mul_le_mul_left _
            (Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left totalSize 4)) 2)) 1
        simp only [List.length_cons]
        nlinarith
      · rw [Machine.run_add,firstRun,Option.bind_some,bodyStore]
        exact tailRun

end Counting.StackMachine.RealizabilityCheck
