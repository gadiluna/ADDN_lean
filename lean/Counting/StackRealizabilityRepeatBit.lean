import Counting.StackRoutineBasic

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false

theorem repeatPushBit_executes (counter output : Fin (registers+2)) (different : counter≠output)
    (bit : Bool) (store : Store registers) (bits : List Bool) (counted : store counter=bits) :
    Executes (forEach counter (pushBit output bit)) store (3*bits.length+1)
      (Function.update (Function.update store counter []) output
        (List.replicate bits.length bit++store output)) := by
  induction bits generalizing store with
  | nil =>
    obtain ⟨ran,halted⟩ := repeat_empty counter (pushBit output bit) store counted
    refine ⟨⟨1,store⟩,by simpa using ran,halted,?_⟩
    have cleared : Function.update store counter []=store := by rw [←counted,Function.update_eq_self]
    simp [cleared]
  | cons top bits ih =>
    let consumed := Function.update store counter bits
    have pushing := pushBit_executes output bit consumed
    have sameOutput : consumed output=store output := by simp [consumed,different.symm]
    rw [sameOutput] at pushing
    let middle := Function.update consumed output (bit::store output)
    obtain ⟨bodyFinish,bodyRun,bodyHalted,bodyStore⟩ := pushing
    obtain ⟨tailFinish,tailRun,tailHalted,tailStore⟩ := ih middle (by simp [middle,consumed,different])
    have iteration := repeat_iteration counter (pushBit output bit) store top bits counted 1 bodyFinish bodyRun bodyHalted
    have total : 3*(top::bits).length+1=3+(3*bits.length+1) := by simp;omega
    refine ⟨tailFinish,?_,tailHalted,?_⟩
    · rw [total,Machine.run_add,iteration,Option.bind_some,bodyStore]
      exact tailRun
    · apply tailStore.trans
      funext r
      by_cases atOutput : r=output
      · subst r
        simp [middle,consumed,List.replicate_succ',List.append_assoc]
      · by_cases atCounter : r=counter
        · subst r;simp [middle,consumed,different]
        · simp [middle,consumed,atOutput,atCounter]

end Counting.StackMachine.RealizabilityCheck
