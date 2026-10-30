import Counting.StackRealizabilityReachRow

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def checkSource (width : Nat) (arcs active : List Bool) (source : Nat) : Bool:=
  !RealizabilityVerifier.BitGraph.bitAt active source || implicationFold width active (rowSeen width arcs source) true

def rowsFold (width : Nat) (arcs active : List Bool) : Nat → Nat → Bool → Bool
  | _,0,value=>value
  | start,count+1,value=>rowsFold width arcs active (start+1) count (value && checkSource width arcs active start)

def rowsStore (store : Store 22) (count : Nat) (value : Bool) (tail : List Bool) : Store 22:=
  Function.update (Function.update (Function.update store 23 [])
    19 (rowsFold (store 2).length (store 0) (store 18) (store 17).length count value::tail))
    17 (List.replicate count true++store 17)

theorem rows_executes (store : Store 22) (counter : List Bool) (counted : store 23=counter)
    (value : Bool) (tail : List Bool) (accumulated : store 19=value::tail) (empty : RowEmpty store) :
    ∃ time ≤ counter.length*(202000*((store 0).length+(store 18).length+(store 2).length+
        (store 17).length+counter.length+1)^5+2)+1,
      Executes (forEach 23 rowItem) store time (rowsStore store counter.length value tail):=by
  induction counter generalizing store value with
  | nil=>
    obtain ⟨ran,halted⟩:=repeat_empty (23:Fin 24) rowItem store counted
    have final : rowsStore store 0 value tail=store:=by
      funext r
      by_cases n17 : r=17 <;> by_cases n19 : r=19 <;> by_cases n23 : r=23 <;>
        simp [rowsStore,rowsFold,n17,n19,n23,counted,accumulated]
    exact ⟨1,by simp,⟨1,store⟩,ran,halted,final.symm⟩
  | cons bit counter ih=>
    let consumed:=Function.update store 23 counter
    obtain ⟨bodyTime,bodyBound,finishBody,bodyRun,bodyHalted,bodyStore⟩:=rowItem_executes consumed value tail
      (by simp [consumed,accumulated])
      (by intro r n0 n2 n17 n18 n19 n23;simp [consumed,n23,empty r n0 n2 n17 n18 n19 n23])
    let middle:=rowItemStore consumed value tail
    let next:=value && checkSource (store 2).length (store 0) (store 18) (store 17).length
    obtain ⟨tailTime,tailBound,finishTail,tailRun,tailHalted,tailStore⟩:=ih middle
      (by simp [middle,rowItemStore,consumed]) next
      (by simp [middle,rowItemStore,consumed,rowValue,rowReachable,next,checkSource])
      (by intro r n0 n2 n17 n18 n19 n23;
          simp [middle,rowItemStore,consumed,n17,n19,n23,empty r n0 n2 n17 n18 n19 n23])
    have firstRun:=repeat_iteration (23:Fin 24) rowItem store bit counter counted bodyTime finishBody bodyRun bodyHalted
    have final : rowsStore middle counter.length next tail=rowsStore store (bit::counter).length value tail:=by
      funext r
      by_cases n17 : r=17 <;> by_cases n19 : r=19 <;> by_cases n23 : r=23 <;>
        simp [rowsStore,rowsFold,middle,rowItemStore,consumed,next,n17,n19,n23,
          List.replicate_succ',List.append_assoc]
    refine ⟨bodyTime+2+tailTime,?_,finishTail,?_,tailHalted,tailStore.trans final⟩
    · have tailSize : (middle 0).length+(middle 18).length+(middle 2).length+
          (middle 17).length+counter.length+1=
          (store 0).length+(store 18).length+(store 2).length+(store 17).length+(bit::counter).length+1:=by
        simp [middle,rowItemStore,consumed];omega
      rw [tailSize] at tailBound
      simp only [consumed,Function.update_of_ne (by decide : (0:Fin 24)≠23),
        Function.update_of_ne (by decide : (18:Fin 24)≠23),Function.update_of_ne (by decide : (2:Fin 24)≠23),
        Function.update_of_ne (by decide : (17:Fin 24)≠23)] at bodyBound
      let S:=(store 0).length+(store 18).length+(store 2).length+(store 17).length+(bit::counter).length+1
      have bodyLimit : bodyTime ≤ 202000*S^5:=by
        apply bodyBound.trans
        exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp only [S];omega) 5)
      change bodyTime+2+tailTime ≤ (bit::counter).length*(202000*S^5+2)+1
      change tailTime ≤ counter.length*(202000*S^5+2)+1 at tailBound
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
    · rw [Machine.run_add,firstRun,Option.bind_some,bodyStore]
      exact tailRun

end Counting.StackMachine.RealizabilityCheck
