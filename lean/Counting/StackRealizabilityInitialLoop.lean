import Counting.StackRealizabilityInitialSpec

namespace Counting.StackMachine.RealizabilityCheck
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

def initialLoopStore (store : Store 24) (nodes : List Executable.Node) (start leaders nonleaders : Nat)
    (values : List Nat) (suffix : List Bool) : Store 24:=
  Function.update (Function.update (Function.update (Function.update (Function.update store 23 []) 20 suffix)
    21 (leaders+initialRangeSum nodes true start values).bits)
    22 (nonleaders+initialRangeSum nodes false start values).bits)
      18 (List.replicate values.length true++store 18)

theorem initialLoop_executes (store : Store 24) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀ r : Fin 26,r.val<17 → r≠1 → store r=[])
    (e19 : store 19=[]) (e24 : store 24=[]) (e25 : store 25=[])
    (nodes : List Executable.Node) (start : Nat) (values : List Nat) (inside : start+values.length≤nodes.length)
    (nodeSuffix : List Bool) (nodeInput : store 17=Encoding.sequence Encoding.node nodes++nodeSuffix)
    (indexCounter : (store 18).length=start)
    (leaders nonleaders : Nat) (first : store 21=leaders.bits) (second : store 22=nonleaders.bits)
    (suffix : List Bool) (input : store 20=Encoding.sequence Encoding.natural values++suffix)
    (bits : List Bool) (counter : store 23=bits) (countEq : bits.length=values.length) :
    ∃ time ≤ values.length*(8000*((store 17).length+(store 20).length+leaders.size+nonleaders.size+1)^4+2)+1,
      Executes (forEach 23 initialItem) store time (initialLoopStore store nodes start leaders nonleaders values suffix):=by
  induction values generalizing store start leaders nonleaders bits with
  | nil=>
    have emptyBits : bits=[]:=List.length_eq_zero_iff.mp countEq
    have empty : store 23=[]:=counter.trans emptyBits
    have source : store 20=suffix:=by simpa only [Encoding.sequence,List.nil_append] using input
    obtain ⟨ran,halted⟩:=repeat_empty (23:Fin 26) initialItem store empty
    have final : initialLoopStore store nodes start leaders nonleaders [] suffix=store:=by
      funext r
      by_cases r18 : r=18 <;> by_cases r20 : r=20 <;> by_cases r21 : r=21 <;>
        by_cases r22 : r=22 <;> by_cases r23 : r=23 <;>
        simp [initialLoopStore,initialRangeSum,r18,r20,r21,r22,r23,empty,source,first,second]
    exact ⟨1,by simp,⟨1,store⟩,ran,halted,final.symm⟩
  | cons value values ih=>
    cases bits with
    | nil=>simp at countEq
    | cons bit bits=>
      have indexBound : start<nodes.length:=by simp only [List.length_cons] at inside;omega
      let index : Fin nodes.length:=⟨start,indexBound⟩
      let consumed:=Function.update store 23 bits
      let remaining:=Encoding.sequence Encoding.natural values++suffix
      have consumedWork (r : Fin 26) (small : r.val<17) (different : r≠1) : consumed r=[]:=by
        have n23 : r≠23:=by intro same;subst r;norm_num at small
        simp [consumed,n23,work r small different]
      have headInput : consumed 20=Encoding.natural.encode value++remaining:=by
        simpa only [consumed,Function.update_of_ne (by decide : (20:Fin 26)≠23),
          Encoding.sequence,List.append_assoc] using input
      obtain ⟨bodyTime,bodyBound,finishBody,bodyRun,bodyHalt,bodyStore⟩:=initialItem_executes consumed accepted tail
        (by simp [consumed,status]) consumedWork (by simp [consumed,e19])
        (by simp [consumed,e24]) (by simp [consumed,e25]) nodes index nodeSuffix
        (by simp [consumed,nodeInput]) (by simp [consumed,index,indexCounter]) leaders nonleaders value
        (by simp [consumed,first]) (by simp [consumed,second]) remaining headInput
      let middle:=initialItemStore consumed nodes[index] leaders nonleaders value remaining
      let nextLeaders:=leaders+initialContribution nodes[index] true value
      let nextNonleaders:=nonleaders+initialContribution nodes[index] false value
      have middleWork (r : Fin 26) (small : r.val<17) (different : r≠1) : middle r=[]:=by
        have n18 : r≠18:=by intro same;subst r;norm_num at small
        have n20 : r≠20:=by intro same;subst r;norm_num at small
        have n21 : r≠21:=by intro same;subst r;norm_num at small
        have n22 : r≠22:=by intro same;subst r;norm_num at small
        simp [middle,initialItemStore,n18,n20,n21,n22,consumedWork r small different]
      have sourceSame : middle 17=store 17:=by simp [middle,initialItemStore,consumed]
      obtain ⟨tailTime,tailBound,finishTail,tailRun,tailHalt,tailStore⟩:=ih middle
        (by simp [middle,initialItemStore,consumed,status]) middleWork
        (by simp [middle,initialItemStore,consumed,e19]) (by simp [middle,initialItemStore,consumed,e24])
        (by simp [middle,initialItemStore,consumed,e25]) (start+1) (by simp only [List.length_cons] at inside;omega)
        (sourceSame.trans nodeInput) (by simp [middle,initialItemStore,consumed,indexCounter])
        nextLeaders nextNonleaders (by simp [middle,initialItemStore,nextLeaders])
        (by simp [middle,initialItemStore,nextNonleaders]) (by simp [middle,initialItemStore,remaining])
        bits (by simp [middle,initialItemStore,consumed]) (by simpa using countEq)
      have firstRun:=repeat_iteration (23:Fin 26) initialItem store bit bits counter bodyTime finishBody bodyRun bodyHalt
      have selected : nodes[index]=nodes[start]?.getD default:=by simp [index,indexBound]
      have final : initialLoopStore middle nodes (start+1) nextLeaders nextNonleaders values suffix=
          initialLoopStore store nodes start leaders nonleaders (value::values) suffix:=by
        funext r
        by_cases r18 : r=18 <;> by_cases r20 : r=20 <;> by_cases r21 : r=21 <;>
          by_cases r22 : r=22 <;> by_cases r23 : r=23 <;>
          simp [initialLoopStore,initialRangeSum,middle,initialItemStore,consumed,
            nextLeaders,nextNonleaders,selected,r18,r20,r21,r22,r23,Nat.add_assoc,
            List.replicate_succ',List.append_assoc]
      refine ⟨bodyTime+2+tailTime,?_,finishTail,?_,tailHalt,tailStore.trans final⟩
      · have nodeSame : consumed 17=store 17:=by simp [consumed]
        have weightSame : consumed 20=store 20:=by simp [consumed]
        rw [nodeSame,weightSame] at bodyBound
        rw [sourceSame] at tailBound
        have sourceSize : (middle 20).length+nextLeaders.size+nextNonleaders.size≤
            (store 20).length+leaders.size+nonleaders.size:=by
          have sizeBound:=initial_totals_size nodes[index] leaders nonleaders value
          rw [input]
          simp only [middle,initialItemStore,Function.update_of_ne (by decide : (20:Fin 26)≠18),
            Function.update_of_ne (by decide : (20:Fin 26)≠22),
            Function.update_of_ne (by decide : (20:Fin 26)≠21),Function.update_self]
          simp only [remaining,Encoding.sequence,List.length_append,Encoding.natural_length]
          dsimp only [nextLeaders,nextNonleaders]
          omega
        have tailLimit : tailTime≤values.length*(8000*
            ((store 17).length+(store 20).length+leaders.size+nonleaders.size+1)^4+2)+1:=by
          apply tailBound.trans
          have totalSize : (store 17).length+(middle 20).length+nextLeaders.size+nextNonleaders.size+1≤
              (store 17).length+(store 20).length+leaders.size+nonleaders.size+1:=by omega
          exact Nat.add_le_add_right (Nat.mul_le_mul_left _
            (Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left totalSize 4)) 2)) 1
        simp only [List.length_cons]
        nlinarith
      · rw [Machine.run_add,firstRun,Option.bind_some,bodyStore]
        exact tailRun

end Counting.StackMachine.RealizabilityCheck
