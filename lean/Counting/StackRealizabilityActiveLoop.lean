import Counting.StackRealizabilityActiveItem

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def activeValues (newBits oldBits outsideBits : List Bool) : Nat → Nat → List Bool
  | _,0=>[]
  | start,count+1=>activeBit newBits oldBits outsideBits start::
      activeValues newBits oldBits outsideBits (start+1) count

@[simp] theorem activeValues_length (newBits oldBits outsideBits : List Bool) (start count : Nat) :
    (activeValues newBits oldBits outsideBits start count).length=count:=by
  induction count generalizing start with
  | zero=>rfl
  | succ count ih=>simp [activeValues,ih]

def activeLoopStore (store : Store 12) (bits : List Bool) : Store 12:=
  Function.update (Function.update (Function.update store 13 [])
    8 ((activeValues (store 0) (store 1) (store 2) (store 3).length bits.length).reverse++store 8))
    3 (List.replicate bits.length true++store 3)

theorem activeLoop_executes (store : Store 12) (bits : List Bool) (counted : store 13=bits)
    (e5 : store 5=[]) (e6 : store 6=[]) (e7 : store 7=[])
    (e10 : store 10=[]) (e11 : store 11=[]) (e12 : store 12=[]) :
    ∃ time ≤ bits.length*(100*((store 0).length+(store 1).length+(store 2).length+
        (store 3).length+bits.length+1)+2)+1,
      Executes (forEach 13 activeItem) store time (activeLoopStore store bits):=by
  induction bits generalizing store with
  | nil=>
    obtain ⟨ran,halted⟩:=repeat_empty (13:Fin 14) activeItem store counted
    have final : activeLoopStore store []=store:=by
      funext r
      by_cases r14 : r=3 <;> by_cases r15 : r=13 <;> by_cases r16 : r=8 <;>
        simp [activeLoopStore,activeValues,r14,r15,r16,counted]
    exact ⟨1,by simp,⟨1,store⟩,ran,halted,final.symm⟩
  | cons bit bits ih=>
    let consumed:=Function.update store 13 bits
    obtain ⟨bodyTime,bodyBound,finishBody,bodyRun,bodyHalted,bodyStore⟩:=activeItem_executes consumed
      (by simp [consumed,e5]) (by simp [consumed,e6]) (by simp [consumed,e7])
      (by simp [consumed,e10]) (by simp [consumed,e11]) (by simp [consumed,e12])
    let middle:=activeItemStore consumed
    obtain ⟨tailTime,tailBound,finishTail,tailRun,tailHalted,tailStore⟩:=ih middle
      (by simp [middle,activeItemStore,consumed])
      (by simp [middle,activeItemStore,consumed,e5]) (by simp [middle,activeItemStore,consumed,e6])
      (by simp [middle,activeItemStore,consumed,e7]) (by simp [middle,activeItemStore,consumed,e10])
      (by simp [middle,activeItemStore,consumed,e11]) (by simp [middle,activeItemStore,consumed,e12])
    have firstRun:=repeat_iteration (13:Fin 14) activeItem store bit bits counted bodyTime finishBody bodyRun bodyHalted
    have final : activeLoopStore middle bits=activeLoopStore store (bit::bits):=by
      funext r
      by_cases r14 : r=3 <;> by_cases r15 : r=13 <;> by_cases r16 : r=8 <;>
        simp [activeLoopStore,middle,activeItemStore,consumed,activeValues,activeBit,
          r14,r15,r16,List.replicate_succ',List.append_assoc]
    refine ⟨bodyTime+2+tailTime,?_,finishTail,?_,tailHalted,tailStore.trans final⟩
    · have tailSize : (middle 0).length+(middle 1).length+(middle 2).length+
          (middle 3).length+bits.length+1=
          (store 0).length+(store 1).length+(store 2).length+(store 3).length+(bit::bits).length+1:=by
        simp [middle,activeItemStore,consumed];omega
      rw [tailSize] at tailBound
      simp only [consumed,Function.update_of_ne (by decide : (0:Fin 14)≠13),
        Function.update_of_ne (by decide : (1:Fin 14)≠13),Function.update_of_ne (by decide : (2:Fin 14)≠13),
        Function.update_of_ne (by decide : (3:Fin 14)≠13)] at bodyBound
      let S:=(store 0).length+(store 1).length+(store 2).length+(store 3).length+(bit::bits).length+1
      have bodyLimit : bodyTime ≤ 100*S:=by
        apply bodyBound.trans
        exact Nat.mul_le_mul_left _ (by dsimp only [S];omega)
      change bodyTime+2+tailTime ≤ (bit::bits).length*(100*S+2)+1
      change tailTime ≤ bits.length*(100*S+2)+1 at tailBound
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
    · rw [Machine.run_add,firstRun,Option.bind_some,bodyStore]
      exact tailRun

end Counting.StackMachine.RealizabilityCheck
