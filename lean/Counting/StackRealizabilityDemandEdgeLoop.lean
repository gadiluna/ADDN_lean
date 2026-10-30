import Counting.StackRealizabilityDemandSpec

namespace Counting.StackMachine.RealizabilityCheck
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def demandEdgeLoopStore (store : Store 30) (level target old value total : Nat)
    (edges : List (Nat×Nat)) (suffix : List Bool) : Store 30:=
  Function.update (Function.update (Function.update store 30 []) 19 suffix)
    26 (total+demandEdges level target old value edges).bits

theorem demandEdgeLoop_executes (store : Store 30) (level target old value total : Nat)
    (levelInput : store 0=level.bits) (targetInput : store 22=target.bits) (oldInput : store 25=old.bits)
    (weight : store 24=value.bits) (accumulator : store 26=total.bits)
    (work : ∀ r : Fin 32,4 ≤ r.val → r.val<17 → store r=[])
    (e2 : store 2=[]) (e27 : store 27=[]) (e28 : store 28=[]) (e29 : store 29=[])
    (edges : List (Nat×Nat)) (suffix : List Bool)
    (input : store 19=Encoding.sequence (Encoding.product Encoding.natural Encoding.natural) edges++suffix)
    (bits : List Bool) (counter : store 30=bits) (countEq : bits.length=edges.length) :
    ∃ time ≤ edges.length*(85000*((store 19).length+level.size+target.size+old.size+value.size+total.size+1+
        edges.length*value.size)^3+2)+1,
      Executes (forEach 30 demandEdge) store time
        (demandEdgeLoopStore store level target old value total edges suffix):=by
  induction edges generalizing store total bits with
  | nil=>
    have emptyBits : bits=[]:=List.length_eq_zero_iff.mp countEq
    have empty : store 30=[]:=counter.trans emptyBits
    have source : store 19=suffix:=by simpa only [Encoding.sequence,List.nil_append] using input
    obtain ⟨ran,halted⟩:=repeat_empty (30:Fin 32) demandEdge store empty
    have final : demandEdgeLoopStore store level target old value total [] suffix=store:=by
      funext r
      by_cases r19 : r=19 <;> by_cases r26 : r=26 <;> by_cases r30 : r=30 <;>
        simp [demandEdgeLoopStore,demandEdges,r19,r26,r30,empty,source,accumulator]
    exact ⟨1,by simp,⟨1,store⟩,ran,halted,final.symm⟩
  | cons edge edges ih=>
    cases bits with
    | nil=>simp at countEq
    | cons bit bits=>
      let consumed:=Function.update store 30 bits
      let remaining:=Encoding.sequence (Encoding.product Encoding.natural Encoding.natural) edges++suffix
      have consumedWork (r : Fin 32) (lo : 4 ≤ r.val) (hi : r.val<17) : consumed r=[]:=by
        have n30 : r≠30:=by intro same;subst r;norm_num at hi
        simp [consumed,n30,work r lo hi]
      have headInput : consumed 19=(Encoding.product Encoding.natural Encoding.natural).encode edge++remaining:=by
        simpa only [consumed,Function.update_of_ne (by decide : (19:Fin 32)≠30),
          Encoding.sequence,List.append_assoc] using input
      obtain ⟨bodyTime,bodyBound,finishBody,bodyRun,bodyHalt,bodyStore⟩:=demandEdge_executes consumed
        level target edge.1 old value edge.2 total
        (by simp [consumed,levelInput]) (by simp [consumed,targetInput]) (by simp [consumed,oldInput])
        (by simp [consumed,weight]) (by simp [consumed,accumulator]) consumedWork
        (by simp [consumed,e2]) (by simp [consumed,e27]) (by simp [consumed,e28])
        (by simp [consumed,e29]) remaining headInput
      let middle:=demandEdgeStore consumed level target edge.1 old value edge.2 total remaining
      let nextTotal:=total+demandContribution level target edge.1 old value edge.2
      have middleWork (r : Fin 32) (lo : 4 ≤ r.val) (hi : r.val<17) : middle r=[]:=by
        have n19 : r≠19:=by intro same;subst r;norm_num at hi
        have n26 : r≠26:=by intro same;subst r;norm_num at hi
        simp [middle,demandEdgeStore,n19,n26,consumedWork r lo hi]
      obtain ⟨tailTime,tailBound,finishTail,tailRun,tailHalt,tailStore⟩:=ih middle nextTotal
        (by simp [middle,demandEdgeStore,consumed,levelInput])
        (by simp [middle,demandEdgeStore,consumed,targetInput])
        (by simp [middle,demandEdgeStore,consumed,oldInput])
        (by simp [middle,demandEdgeStore,consumed,weight])
        (by simp [middle,demandEdgeStore,nextTotal]) middleWork
        (by simp [middle,demandEdgeStore,consumed,e2]) (by simp [middle,demandEdgeStore,consumed,e27])
        (by simp [middle,demandEdgeStore,consumed,e28]) (by simp [middle,demandEdgeStore,consumed,e29])
        (by simp [middle,demandEdgeStore,remaining]) bits
        (by simp [middle,demandEdgeStore,consumed]) (by simpa using countEq)
      have firstRun:=repeat_iteration (30:Fin 32) demandEdge store bit bits counter bodyTime finishBody bodyRun bodyHalt
      have final : demandEdgeLoopStore middle level target old value nextTotal edges suffix=
          demandEdgeLoopStore store level target old value total (edge::edges) suffix:=by
        funext r
        by_cases r19 : r=19 <;> by_cases r26 : r=26 <;> by_cases r30 : r=30 <;>
          simp [demandEdgeLoopStore,demandEdges,middle,demandEdgeStore,consumed,nextTotal,r19,r26,r30,Nat.add_assoc]
      refine ⟨bodyTime+2+tailTime,?_,finishTail,?_,tailHalt,tailStore.trans final⟩
      · have inputSame : consumed 19=store 19:=by simp [consumed]
        rw [inputSame] at bodyBound
        have sourceSize : (middle 19).length+nextTotal.size ≤ (store 19).length+total.size+value.size:=by
          have sizeBound:=demand_total_size level target edge.1 old value edge.2 total
          rw [input]
          simp only [middle,demandEdgeStore,Function.update_of_ne (by decide : (19:Fin 32)≠26),Function.update_self]
          simp only [remaining,Encoding.sequence,Encoding.product,List.length_append,Encoding.natural_length]
          dsimp only [nextTotal]
          omega
        let base:=(store 19).length+level.size+target.size+old.size+value.size+total.size+1+
          (edge::edges).length*value.size
        have bodyLimit : bodyTime ≤ 85000*base^3:=by
          apply bodyBound.trans
          exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp only [base];omega) 3)
        have tailLimit : tailTime ≤ edges.length*(85000*base^3+2)+1:=by
          apply tailBound.trans
          have totalSize : (middle 19).length+level.size+target.size+old.size+value.size+nextTotal.size+1+
              edges.length*value.size ≤ base:=by
            dsimp only [base]
            simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
            omega
          exact Nat.add_le_add_right (Nat.mul_le_mul_left _
            (Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left totalSize 3)) 2)) 1
        change bodyTime+2+tailTime ≤ (edge::edges).length*(85000*base^3+2)+1
        simp only [List.length_cons]
        nlinarith
      · rw [Machine.run_add,firstRun,Option.bind_some,bodyStore]
        exact tailRun

end Counting.StackMachine.RealizabilityCheck
