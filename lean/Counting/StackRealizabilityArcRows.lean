import Counting.StackRealizabilityArcRow

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def arcRowsStore (store : Store 30) (bits : List Bool) : Store 30:=
  Function.update (Function.update (Function.update (Function.update store 31 [])
    24 ((arcTableValues (arcTables store) (store 29).length (store 8).length
      (store 10).length bits.length).reverse++store 24))
    8 (List.replicate bits.length true++store 8))
    10 ((List.replicate bits.length (List.replicate (store 29).length true)).flatten++store 10)

theorem arcRows_executes (store : Store 30) (bits : List Bool) (counted : store 31=bits)
    (flags : ∀r : Fin 32,12≤r.val → r.val<24 → store r=[])
    (e9 : store 9=[]) (e11 : store 11=[]) (e30 : store 30=[])
    (e26 : store 26=[]) (e27 : store 27=[]) (e28 : store 28=[]) :
    ∃ time ≤ bits.length*(10000*(arcReadSize store+(store 29).length+
        bits.length*((store 29).length+1))^3+2)+1,
      Executes (forEach 31 arcRow) store time (arcRowsStore store bits):=by
  induction bits generalizing store with
  | nil=>
    obtain ⟨ran,halted⟩:=repeat_empty (31:Fin 32) arcRow store counted
    have final : arcRowsStore store []=store:=by
      funext r
      by_cases r8 : r=8 <;> by_cases r10 : r=10 <;> by_cases r24 : r=24 <;> by_cases r31 : r=31 <;>
        simp [arcRowsStore,arcTableValues,r8,r10,r24,r31,counted]
    exact ⟨1,by simp,⟨1,store⟩,ran,halted,final.symm⟩
  | cons bit bits ih=>
    let consumed:=Function.update store 31 bits
    have consumedFlags (r : Fin 32) (lo : 12≤r.val) (hi : r.val<24) : consumed r=[]:=by
      have ne : r≠31:=by intro same;subst r;simp at hi
      simp [consumed,Function.update_of_ne ne,flags r lo hi]
    obtain ⟨bodyTime,bodyBound,finishBody,bodyRun,bodyHalted,bodyStore⟩:=arcRow_executes consumed consumedFlags
      (by simp [consumed,e9]) (by simp [consumed,e11]) (by simp [consumed,e30])
      (by simp [consumed,e26]) (by simp [consumed,e27]) (by simp [consumed,e28])
    let middle:=arcRowStore consumed
    have middleFlags (r : Fin 32) (lo : 12≤r.val) (hi : r.val<24) : middle r=[]:=by
      have n8 : r≠8:=by intro same;subst r;simp at lo
      have n10 : r≠10:=by intro same;subst r;simp at lo
      have n24 : r≠24:=by intro same;subst r;simp at hi
      simp [middle,arcRowStore,n8,n10,n24,consumedFlags r lo hi]
    obtain ⟨tailTime,tailBound,finishTail,tailRun,tailHalted,tailStore⟩:=ih middle
      (by simp [middle,arcRowStore,consumed]) middleFlags
      (by simp [middle,arcRowStore,consumed,e9]) (by simp [middle,arcRowStore,consumed,e11])
      (by simp [middle,arcRowStore,consumed,e30]) (by simp [middle,arcRowStore,consumed,e26])
      (by simp [middle,arcRowStore,consumed,e27]) (by simp [middle,arcRowStore,consumed,e28])
    have firstRun:=repeat_iteration (31:Fin 32) arcRow store bit bits counted bodyTime finishBody bodyRun bodyHalted
    have final : arcRowsStore middle bits=arcRowsStore store (bit::bits):=by
      funext r
      by_cases r8 : r=8 <;> by_cases r10 : r=10 <;> by_cases r24 : r=24 <;> by_cases r31 : r=31 <;>
        simp [arcRowsStore,middle,arcRowStore,consumed,arcTableValues,
          r8,r10,r24,r31,List.replicate_succ',List.flatten_append,List.append_assoc,Nat.add_comm]
      all_goals simp only [←List.append_assoc,←List.replicate_add,Nat.add_comm]
    refine ⟨bodyTime+2+tailTime,?_,finishTail,?_,tailHalted,tailStore.trans final⟩
    · have bodySize : arcReadSize consumed+(consumed 29).length=arcReadSize store+(store 29).length:=by
        simp [arcReadSize,consumed]
      rw [bodySize] at bodyBound
      have tailSize : arcReadSize middle+(middle 29).length+bits.length*((middle 29).length+1)=
          arcReadSize store+(store 29).length+(bit::bits).length*((store 29).length+1):=by
        simp [arcReadSize,middle,arcRowStore,consumed,List.length_cons,List.length_append,Nat.add_mul]
        omega
      rw [tailSize] at tailBound
      let S:=arcReadSize store+(store 29).length+(bit::bits).length*((store 29).length+1)
      have bodyLimit : bodyTime≤10000*S^3:=by
        apply bodyBound.trans
        exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp only [S];omega) 3)
      change bodyTime+2+tailTime≤(bit::bits).length*(10000*S^3+2)+1
      change tailTime≤bits.length*(10000*S^3+2)+1 at tailBound
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
    · rw [Machine.run_add,firstRun,Option.bind_some,bodyStore]
      exact tailRun

end Counting.StackMachine.RealizabilityCheck
