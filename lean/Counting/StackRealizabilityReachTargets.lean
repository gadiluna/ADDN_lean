import Counting.StackRealizabilityReachTarget

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Synchronous values for a consecutive interval of explicit target slots. -/
def reachValues (arcs seen : List Bool) (width : Nat) : Nat → Nat → List Bool
  | _,0=>[]
  | start,count+1=>reachFold arcs seen width 0 start width
      (RealizabilityVerifier.BitGraph.bitAt seen start)::reachValues arcs seen width (start+1) count

@[simp] theorem reachValues_length (arcs seen : List Bool) (width start count : Nat) :
    (reachValues arcs seen width start count).length=count:=by
  induction count generalizing start with
  | zero=>rfl
  | succ count ih=>simp [reachValues,ih]

def reachTargetsStore (store : Store 15) (bits : List Bool) : Store 15:=
  Function.update (Function.update (Function.update store 15 [])
    16 ((reachValues (store 0) (store 1) (store 2).length (store 14).length bits.length).reverse++store 16))
    14 (List.replicate bits.length true++store 14)

theorem reachTargets_executes (store : Store 15) (bits : List Bool) (counted : store 15=bits)
    (e3 : store 3=[]) (e4 : store 4=[]) (e5 : store 5=[]) (e6 : store 6=[]) (e7 : store 7=[])
    (e9 : store 9=[]) (e10 : store 10=[]) (e11 : store 11=[]) (e12 : store 12=[]) (e13 : store 13=[]) :
    ∃ time ≤ bits.length*(1000*((store 0).length+(store 1).length+(store 2).length+
        (store 14).length+bits.length+1)^3+2)+1,
      Executes (forEach 15 reachTarget) store time (reachTargetsStore store bits):=by
  induction bits generalizing store with
  | nil=>
    obtain ⟨ran,halted⟩:=repeat_empty (15:Fin 17) reachTarget store counted
    have final : reachTargetsStore store []=store:=by
      funext r
      by_cases r14 : r=14 <;> by_cases r15 : r=15 <;> by_cases r16 : r=16 <;>
        simp [reachTargetsStore,reachValues,r14,r15,r16,counted]
    exact ⟨1,by simp,⟨1,store⟩,ran,halted,final.symm⟩
  | cons bit bits ih=>
    let consumed:=Function.update store 15 bits
    obtain ⟨bodyTime,bodyBound,finishBody,bodyRun,bodyHalted,bodyStore⟩:=reachTarget_executes consumed
      (by simp [consumed,e3]) (by simp [consumed,e4]) (by simp [consumed,e5])
      (by simp [consumed,e6]) (by simp [consumed,e7]) (by simp [consumed,e9])
      (by simp [consumed,e10]) (by simp [consumed,e11]) (by simp [consumed,e12]) (by simp [consumed,e13])
    let middle:=reachTargetStore consumed
    obtain ⟨tailTime,tailBound,finishTail,tailRun,tailHalted,tailStore⟩:=ih middle
      (by simp [middle,reachTargetStore,consumed])
      (by simp [middle,reachTargetStore,consumed,e3]) (by simp [middle,reachTargetStore,consumed,e4])
      (by simp [middle,reachTargetStore,consumed,e5]) (by simp [middle,reachTargetStore,consumed,e6])
      (by simp [middle,reachTargetStore,consumed,e7]) (by simp [middle,reachTargetStore,consumed,e9])
      (by simp [middle,reachTargetStore,consumed,e10]) (by simp [middle,reachTargetStore,consumed,e11])
      (by simp [middle,reachTargetStore,consumed,e12]) (by simp [middle,reachTargetStore,consumed,e13])
    have firstRun:=repeat_iteration (15:Fin 17) reachTarget store bit bits counted bodyTime finishBody bodyRun bodyHalted
    have final : reachTargetsStore middle bits=reachTargetsStore store (bit::bits):=by
      funext r
      by_cases r14 : r=14 <;> by_cases r15 : r=15 <;> by_cases r16 : r=16 <;>
        simp [reachTargetsStore,middle,reachTargetStore,consumed,reachValues,reachTargetValue,
          r14,r15,r16,List.replicate_succ',List.append_assoc]
    refine ⟨bodyTime+2+tailTime,?_,finishTail,?_,tailHalted,tailStore.trans final⟩
    · have tailSize : (middle 0).length+(middle 1).length+(middle 2).length+
          (middle 14).length+bits.length+1=
          (store 0).length+(store 1).length+(store 2).length+(store 14).length+(bit::bits).length+1:=by
        simp [middle,reachTargetStore,consumed];omega
      rw [tailSize] at tailBound
      simp only [consumed,Function.update_of_ne (by decide : (0:Fin 17)≠15),
        Function.update_of_ne (by decide : (1:Fin 17)≠15),Function.update_of_ne (by decide : (2:Fin 17)≠15),
        Function.update_of_ne (by decide : (14:Fin 17)≠15)] at bodyBound
      let S:=(store 0).length+(store 1).length+(store 2).length+(store 14).length+(bit::bits).length+1
      have bodyLimit : bodyTime ≤ 1000*S^3:=by
        apply bodyBound.trans
        exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp only [S];omega) 3)
      change bodyTime+2+tailTime ≤ (bit::bits).length*(1000*S^3+2)+1
      change tailTime ≤ bits.length*(1000*S^3+2)+1 at tailBound
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
    · rw [Machine.run_add,firstRun,Option.bind_some,bodyStore]
      exact tailRun

end Counting.StackMachine.RealizabilityCheck
