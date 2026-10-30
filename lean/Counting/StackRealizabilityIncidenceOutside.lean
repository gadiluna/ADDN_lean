import Counting.StackRealizabilityIncidenceRows

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def incidenceZeroPair : Routine 44 := sequence (pushBit 22 false) (pushBit 37 false)

def incidenceOutsideStore (store : Store 44) (bits : List Bool) : Store 44 :=
  Function.update (Function.update (Function.update store 43 [])
    22 (List.replicate bits.length false++store 22))
    37 (List.replicate bits.length false++store 37)

theorem incidenceOutside_executes (store : Store 44) (bits : List Bool) (counted : store 43=bits) :
    Executes (forEach 43 incidenceZeroPair) store (5*bits.length+1) (incidenceOutsideStore store bits) := by
  induction bits generalizing store with
  | nil =>
    obtain ⟨ran,halted⟩ := repeat_empty (43:Fin 46) incidenceZeroPair store counted
    refine ⟨⟨1,store⟩,by simpa using ran,halted,?_⟩
    funext r
    fin_cases r <;> simp [incidenceOutsideStore,counted]
  | cons bit bits ih =>
    let consumed := Function.update store 43 bits
    let middle := Function.update (Function.update consumed 22 (false::store 22)) 37 (false::store 37)
    have first := pushBit_executes (22:Fin 46) false consumed
    have second := pushBit_executes (37:Fin 46) false (Function.update consumed 22 (false::store 22))
    simp only [consumed,Function.update_of_ne (by decide : (22:Fin 46)≠43)] at first
    simp only [consumed,Function.update_of_ne (by decide : (37:Fin 46)≠22),
      Function.update_of_ne (by decide : (37:Fin 46)≠43)] at second
    obtain ⟨bodyFinish,bodyRun,bodyHalted,bodyStore⟩ := first.sequence second
    obtain ⟨tailFinish,tailRun,tailHalted,tailStore⟩ := ih middle (by simp [middle,consumed])
    have iteration := repeat_iteration (43:Fin 46) incidenceZeroPair store bit bits counted 3
      bodyFinish bodyRun bodyHalted
    have total : 5*(bit::bits).length+1=5+(5*bits.length+1) := by simp;omega
    refine ⟨tailFinish,?_,tailHalted,?_⟩
    · rw [total,Machine.run_add,iteration,Option.bind_some,bodyStore]
      exact tailRun
    · apply tailStore.trans
      funext r
      by_cases n22 : r=22 <;> by_cases n37 : r=37 <;> by_cases n43 : r=43 <;>
        simp [incidenceOutsideStore,middle,consumed,n22,n37,n43,List.replicate_succ',List.append_assoc]

end Counting.StackMachine.RealizabilityCheck
