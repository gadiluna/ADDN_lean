import Counting.StackRealizabilityArcItem

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def arcLoopStore (store : Store 30) (bits : List Bool) : Store 30:=
  Function.update (Function.update (Function.update (Function.update (Function.update store 30 [])
    24 ((arcRowValues (arcTables store) (store 29).length (store 8).length (store 9).length
      (store 10).length (store 11).length bits.length).reverse++store 24))
    9 (List.replicate bits.length true++store 9))
    10 (List.replicate bits.length true++store 10))
    11 ((List.replicate bits.length (store 29)).flatten++store 11)

theorem arcLoop_executes (store : Store 30) (bits : List Bool) (counted : store 30=bits)
    (flags : ∀r : Fin 32,12≤r.val → r.val<24 → store r=[])
    (e26 : store 26=[]) (e27 : store 27=[]) (e28 : store 28=[]) :
    ∃ time ≤ bits.length*(1100*(arcReadSize store+(store 29).length+
        bits.length*((store 29).length+2))+2)+1,
      Executes (forEach 30 arcItem) store time (arcLoopStore store bits):=by
  induction bits generalizing store with
  | nil=>
    obtain ⟨ran,halted⟩:=repeat_empty (30:Fin 32) arcItem store counted
    have final : arcLoopStore store []=store:=by
      funext r
      by_cases r9 : r=9 <;> by_cases r10 : r=10 <;> by_cases r11 : r=11 <;>
        by_cases r24 : r=24 <;> by_cases r30 : r=30 <;>
        simp [arcLoopStore,arcRowValues,r9,r10,r11,r24,r30,counted]
    exact ⟨1,by simp,⟨1,store⟩,ran,halted,final.symm⟩
  | cons bit bits ih=>
    let consumed:=Function.update store 30 bits
    have consumedFlags (r : Fin 32) (lo : 12≤r.val) (hi : r.val<24) : consumed r=[]:=by
      have ne : r≠30:=by intro same;subst r;simp at hi
      simp [consumed,Function.update_of_ne ne,flags r lo hi]
    obtain ⟨bodyTime,bodyBound,finishBody,bodyRun,bodyHalted,bodyStore⟩:=arcItem_executes consumed consumedFlags
      (by simp [consumed,e26]) (by simp [consumed,e27]) (by simp [consumed,e28])
    let middle:=arcItemStore consumed
    have middleFlags (r : Fin 32) (lo : 12≤r.val) (hi : r.val<24) : middle r=[]:=by
      have n9 : r≠9:=by intro same;subst r;simp at lo
      have n10 : r≠10:=by intro same;subst r;simp at lo
      have n11 : r≠11:=by intro same;subst r;simp at lo
      have n24 : r≠24:=by intro same;subst r;simp at hi
      simp [middle,arcItemStore,n9,n10,n11,n24,consumedFlags r lo hi]
    obtain ⟨tailTime,tailBound,finishTail,tailRun,tailHalted,tailStore⟩:=ih middle
      (by simp [middle,arcItemStore,consumed]) middleFlags
      (by simp [middle,arcItemStore,consumed,e26]) (by simp [middle,arcItemStore,consumed,e27])
      (by simp [middle,arcItemStore,consumed,e28])
    have firstRun:=repeat_iteration (30:Fin 32) arcItem store bit bits counted bodyTime finishBody bodyRun bodyHalted
    have final : arcLoopStore middle bits=arcLoopStore store (bit::bits):=by
      funext r
      by_cases r9 : r=9 <;> by_cases r10 : r=10 <;> by_cases r11 : r=11 <;>
        by_cases r24 : r=24 <;> by_cases r30 : r=30 <;>
        simp [arcLoopStore,middle,arcItemStore,consumed,arcRowValues,arcPointValue_cell,
          r9,r10,r11,r24,r30,List.replicate_succ',List.flatten_append,List.append_assoc,Nat.add_comm]
    refine ⟨bodyTime+2+tailTime,?_,finishTail,?_,tailHalted,tailStore.trans final⟩
    · have bodySize : arcReadSize consumed+(consumed 29).length=arcReadSize store+(store 29).length:=by
        simp [arcReadSize,consumed]
      rw [bodySize] at bodyBound
      have tailSize : arcReadSize middle+(middle 29).length+bits.length*((middle 29).length+2)=
          arcReadSize store+(store 29).length+(bit::bits).length*((store 29).length+2):=by
        simp [arcReadSize,middle,arcItemStore,consumed,List.length_cons,List.length_append,Nat.add_mul]
        omega
      rw [tailSize] at tailBound
      let S:=arcReadSize store+(store 29).length+(bit::bits).length*((store 29).length+2)
      have bodyLimit : bodyTime≤1100*S:=by apply bodyBound.trans;dsimp only [S];omega
      change bodyTime+2+tailTime≤(bit::bits).length*(1100*S+2)+1
      change tailTime≤bits.length*(1100*S+2)+1 at tailBound
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
    · rw [Machine.run_add,firstRun,Option.bind_some,bodyStore]
      exact tailRun

end Counting.StackMachine.RealizabilityCheck
