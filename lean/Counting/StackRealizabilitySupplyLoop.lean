import Counting.StackRealizabilitySupplySpec

namespace Counting.StackMachine.RealizabilityCheck
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def supplyLoopStore (store : Store 28) (nodes : List Executable.Node) (target old start total : Nat)
    (values : List Nat) (suffix : List Bool) : Store 28:=
  Function.update (Function.update (Function.update (Function.update store 23 []) 20 suffix)
    26 (total+supplyRangeSum nodes target old start values).bits)
      18 (List.replicate values.length true++store 18)

theorem supplyLoop_executes (store : Store 28) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀ r : Fin 30,r.val<17 → r≠1 → store r=[])
    (e19 : store 19=[]) (e24 : store 24=[]) (e27 : store 27=[]) (e28 : store 28=[]) (e29 : store 29=[])
    (nodes : List Executable.Node) (start : Nat) (values : List Nat) (inside : start+values.length ≤ nodes.length)
    (nodeSuffix : List Bool) (nodeInput : store 17=Encoding.sequence Encoding.node nodes++nodeSuffix)
    (indexCounter : (store 18).length=start)
    (target old total : Nat) (level : store 22=target.bits) (parent : store 25=(old+1).bits)
    (accumulator : store 26=total.bits)
    (suffix : List Bool) (input : store 20=Encoding.sequence Encoding.natural values++suffix)
    (bits : List Bool) (counter : store 23=bits) (countEq : bits.length=values.length) :
    ∃ time ≤ values.length*(100000*((store 17).length+(store 20).length+total.size+
        target.size+(old+1).size+1+values.length*(store 17).length)^4+2)+1,
      Executes (forEach 23 supplyItem) store time (supplyLoopStore store nodes target old start total values suffix):=by
  induction values generalizing store start total bits with
  | nil=>
    have emptyBits : bits=[]:=List.length_eq_zero_iff.mp countEq
    have empty : store 23=[]:=counter.trans emptyBits
    have source : store 20=suffix:=by simpa only [Encoding.sequence,List.nil_append] using input
    obtain ⟨ran,halted⟩:=repeat_empty (23:Fin 30) supplyItem store empty
    have final : supplyLoopStore store nodes target old start total [] suffix=store:=by
      funext r
      by_cases r18 : r=18 <;> by_cases r20 : r=20 <;> by_cases r26 : r=26 <;>
        by_cases r23 : r=23 <;>
        simp [supplyLoopStore,supplyRangeSum,r18,r20,r26,r23,empty,source,accumulator]
    exact ⟨1,by simp,⟨1,store⟩,ran,halted,final.symm⟩
  | cons value values ih=>
    cases bits with
    | nil=>simp at countEq
    | cons bit bits=>
      have indexBound : start<nodes.length:=by simp only [List.length_cons] at inside;omega
      let index : Fin nodes.length:=⟨start,indexBound⟩
      let consumed:=Function.update store 23 bits
      let remaining:=Encoding.sequence Encoding.natural values++suffix
      have consumedWork (r : Fin 30) (small : r.val<17) (different : r≠1) : consumed r=[]:=by
        have n23 : r≠23:=by intro same;subst r;norm_num at small
        simp [consumed,n23,work r small different]
      have headInput : consumed 20=Encoding.natural.encode value++remaining:=by
        simpa only [consumed,Function.update_of_ne (by decide : (20:Fin 30)≠23),
          Encoding.sequence,List.append_assoc] using input
      obtain ⟨bodyTime,bodyBound,finishBody,bodyRun,bodyHalt,bodyStore⟩:=supplyItem_executes consumed accepted tail
        (by simp [consumed,status]) consumedWork (by simp [consumed,e19])
        (by simp [consumed,e24]) (by simp [consumed,e27]) (by simp [consumed,e28]) (by simp [consumed,e29]) nodes index nodeSuffix
        (by simp [consumed,nodeInput]) (by simp [consumed,index,indexCounter]) target old total value
        (by simp [consumed,level]) (by simp [consumed,parent]) (by simp [consumed,accumulator]) remaining headInput
      let middle:=supplyItemStore consumed nodes[index] target old total value remaining
      let nextTotal:=total+supplyContribution nodes[index] target old value
      have middleWork (r : Fin 30) (small : r.val<17) (different : r≠1) : middle r=[]:=by
        have n18 : r≠18:=by intro same;subst r;norm_num at small
        have n20 : r≠20:=by intro same;subst r;norm_num at small
        have n26 : r≠26:=by intro same;subst r;norm_num at small
        simp [middle,supplyItemStore,n18,n20,n26,consumedWork r small different]
      have sourceSame : middle 17=store 17:=by simp [middle,supplyItemStore,consumed]
      obtain ⟨tailTime,tailBound,finishTail,tailRun,tailHalt,tailStore⟩:=ih middle
        (by simp [middle,supplyItemStore,consumed,status]) middleWork
        (by simp [middle,supplyItemStore,consumed,e19]) (by simp [middle,supplyItemStore,consumed,e24])
        (by simp [middle,supplyItemStore,consumed,e27]) (by simp [middle,supplyItemStore,consumed,e28])
        (by simp [middle,supplyItemStore,consumed,e29]) (start+1) (by simp only [List.length_cons] at inside;omega)
        (sourceSame.trans nodeInput) (by simp [middle,supplyItemStore,consumed,indexCounter])
        nextTotal (by simp [middle,supplyItemStore,consumed,level])
        (by simp [middle,supplyItemStore,consumed,parent]) (by simp [middle,supplyItemStore,nextTotal])
        (by simp [middle,supplyItemStore,remaining]) bits
        (by simp [middle,supplyItemStore,consumed]) (by simpa using countEq)
      have firstRun:=repeat_iteration (23:Fin 30) supplyItem store bit bits counter bodyTime finishBody bodyRun bodyHalt
      have selected : nodes[index]=nodes[start]?.getD default:=by simp [index,indexBound]
      have final : supplyLoopStore middle nodes target old (start+1) nextTotal values suffix=
          supplyLoopStore store nodes target old start total (value::values) suffix:=by
        funext r
        by_cases r18 : r=18 <;> by_cases r20 : r=20 <;> by_cases r26 : r=26 <;> by_cases r23 : r=23 <;>
          simp [supplyLoopStore,supplyRangeSum,middle,supplyItemStore,consumed,nextTotal,selected,
            r18,r20,r26,r23,Nat.add_assoc,List.replicate_succ',List.append_assoc]
      refine ⟨bodyTime+2+tailTime,?_,finishTail,?_,tailHalt,tailStore.trans final⟩
      · have nodeSame : consumed 17=store 17:=by simp [consumed]
        have weightSame : consumed 20=store 20:=by simp [consumed]
        rw [nodeSame,weightSame] at bodyBound
        rw [sourceSame] at tailBound
        have degreeBound : nodes[index].degree.size ≤ (store 17).length:=by
          have fields:=node_supply_fields_size nodes[index]
          have member:=DagValidation.node_sequence_member_le nodes nodes[index] (List.getElem_mem index.isLt)
          rw [nodeInput,List.length_append]
          omega
        have sourceSize : (middle 20).length+nextTotal.size ≤ (store 20).length+total.size+(store 17).length:=by
          have sizeBound:=supply_total_size nodes[index] target old total value
          rw [input]
          simp only [middle,supplyItemStore,Function.update_of_ne (by decide : (20:Fin 30)≠18),
            Function.update_of_ne (by decide : (20:Fin 30)≠26),Function.update_self]
          simp only [remaining,Encoding.sequence,List.length_append,Encoding.natural_length]
          dsimp only [nextTotal]
          omega
        let base:=(store 17).length+(store 20).length+total.size+target.size+(old+1).size+1+
          (value::values).length*(store 17).length
        have bodyLimit : bodyTime ≤ 100000*base^4:=by
          apply bodyBound.trans
          exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp only [base];omega) 4)
        have tailLimit : tailTime ≤ values.length*(100000*base^4+2)+1:=by
          apply tailBound.trans
          have totalSize : (store 17).length+(middle 20).length+nextTotal.size+target.size+(old+1).size+1+
              values.length*(store 17).length ≤ base:=by
            dsimp only [base]
            simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
            omega
          exact Nat.add_le_add_right (Nat.mul_le_mul_left _
            (Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left totalSize 4)) 2)) 1
        change bodyTime+2+tailTime ≤ (value::values).length*(100000*base^4+2)+1
        simp only [List.length_cons]
        nlinarith
      · rw [Machine.run_add,firstRun,Option.bind_some,bodyStore]
        exact tailRun

end Counting.StackMachine.RealizabilityCheck
