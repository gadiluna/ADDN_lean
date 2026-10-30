import Counting.StackNaturalPowerStep
import Counting.StackRoutineBoundedLoop

namespace Counting.StackMachine.NaturalPower
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

def iterationCost (baseLength bound : Nat) := 100000*((bound+1)*baseLength+2)^3

def powerLoop (extra : Nat) (w : Workspace extra) : Routine (extra+13) :=
  forEach (w 13) (multiplyStep extra w)

theorem powerLoop_executes (extra : Nat) (w : Workspace extra) (count bound : Nat)
    (store : Fin (extra+15) → List Bool) (start : Nat)
    (accumulator : store (w 1)=(Encoding.value (store (w 0))^start).bits)
    (counter : store (w 13)=List.replicate count true) (bounded : start+count ≤ bound)
    (empty : ∀ i : Fin 15,i≠0 → i≠1 → i≠13 → store (w i)=[]) :
    ∃ time ≤ count*(iterationCost (store (w 0)).length bound+2)+1,
      Executes (powerLoop extra w) store time
        (Function.update (Function.update store (w 13) []) (w 1)
          (Encoding.value (store (w 0))^(start+count)).bits) := by
  induction count generalizing store start with
  | zero =>
    obtain ⟨ran,halted⟩ := repeat_empty (w 13) (multiplyStep extra w) store counter
    refine ⟨1,by simp,⟨1,store⟩,ran,halted,?_⟩
    simp only [Nat.add_zero,←accumulator]
    have counterEmpty : store (w 13)=[] := counter
    rw [←counterEmpty,Function.update_eq_self,Function.update_eq_self]
  | succ count ih =>
    let consumed := Function.update store (w 13) (List.replicate count true)
    have consumedEmpty (i : Fin 15) (n0 : i≠0) (n1 : i≠1) (n13 : i≠13) : consumed (w i)=[] := by
      simpa [consumed,w.injective.eq_iff,n13] using empty i n0 n1 n13
    obtain ⟨bodyTime,bodyBound,bodyFinish,bodyRun,bodyHalt,bodyStore⟩ := multiplyStep_executes extra w consumed consumedEmpty
    let next := Function.update consumed (w 1) (Encoding.value (store (w 0))^(start+1)).bits
    have bodyResult : bodyFinish.store=next := by
      simpa [next,consumed,w.injective.eq_iff,accumulator,Encoding.value_bits,pow_succ'] using bodyStore
    have nextBase : next (w 0)=store (w 0) := by simp [next,consumed,w.injective.eq_iff]
    have nextAccumulator : next (w 1)=(Encoding.value (next (w 0))^(start+1)).bits := by rw [nextBase];simp [next]
    have nextCounter : next (w 13)=List.replicate count true := by simp [next,consumed,w.injective.eq_iff]
    have nextEmpty (i : Fin 15) (n0 : i≠0) (n1 : i≠1) (n13 : i≠13) : next (w i)=[] := by
      simpa [next,w.injective.eq_iff,n1] using consumedEmpty i n0 n1 n13
    obtain ⟨tailTime,tailBound,tailFinish,tailRun,tailHalt,tailStore⟩ := ih next (start+1) nextAccumulator nextCounter (by omega) nextEmpty
    have firstRun := repeat_iteration (w 13) (multiplyStep extra w) store true (List.replicate count true)
      (by simpa only [List.replicate_succ] using counter) bodyTime bodyFinish bodyRun bodyHalt
    change Machine.run (step (powerLoop extra w).program) (bodyTime+2) ⟨0,store⟩=some ⟨0,bodyFinish.store⟩ at firstRun
    have baseAt : consumed (w 0)=store (w 0) := by simp [consumed,w.injective.eq_iff]
    have accumulatorAt : consumed (w 1)=store (w 1) := by simp [consumed,w.injective.eq_iff]
    rw [baseAt,accumulatorAt,accumulator] at bodyBound
    have length := power_bits_length (store (w 0)) start
    have inputBound : (store (w 0)).length+(Encoding.value (store (w 0))^start).bits.length+1 ≤
        (bound+1)*(store (w 0)).length+2 := by nlinarith
    have bodyLimit : bodyTime ≤ iterationCost (store (w 0)).length bound :=
      bodyBound.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left inputBound _))
    rw [nextBase] at tailBound
    refine ⟨bodyTime+2+tailTime,by nlinarith only [bodyLimit,tailBound],tailFinish,?_,tailHalt,?_⟩
    · rw [Machine.run_add,firstRun,Option.bind_some,bodyResult]
      exact tailRun
    · rw [tailStore,nextBase]
      have index : start+1+count=start+(count+1) := by omega
      rw [index]
      funext r
      by_cases e1 : r=w 1
      · subst r;simp
      · by_cases e13 : r=w 13
        · subst r;simp [w.injective.eq_iff]
        · simp [next,consumed,e1,e13]

/-- Repeated binary multiplication. Only the exponent is unary; the
potentially exponential value is always stored by its binary digits. -/
def powerRoutine (extra : Nat) (w : Workspace extra) : Routine (extra+13) :=
  sequence (pushBit (w 1) true) (powerLoop extra w)

theorem powerRoutine_executes (extra : Nat) (w : Workspace extra) (store : Fin (extra+15) → List Bool)
    (count : Nat) (counter : store (w 13)=List.replicate count true)
    (empty : ∀ i : Fin 15,i≠0 → i≠13 → store (w i)=[]) :
    ∃ time ≤ count*(iterationCost (store (w 0)).length count+2)+3,
      Executes (powerRoutine extra w) store time
        (Function.update (Function.update store (w 13) []) (w 1) (Encoding.value (store (w 0))^count).bits) := by
  let initialized := Function.update store (w 1) [true]
  have pushing : Executes (pushBit (w 1) true) store 1 initialized := by
    simpa [initialized,empty] using pushBit_executes (w 1) true store
  have initializedEmpty (i : Fin 15) (n0 : i≠0) (n1 : i≠1) (n13 : i≠13) : initialized (w i)=[] := by
    simp [initialized,w.injective.eq_iff,n1,empty i n0 n13]
  obtain ⟨time,bound,ran⟩ := powerLoop_executes extra w count count initialized 0
    (by simp [initialized]) (by simp [initialized,w.injective.eq_iff,counter]) (by omega) initializedEmpty
  have baseAt : initialized (w 0)=store (w 0) := by simp [initialized,w.injective.eq_iff]
  rw [baseAt,Nat.zero_add] at ran
  rw [baseAt] at bound
  have final : Function.update (Function.update initialized (w 13) []) (w 1)
      (Encoding.value (store (w 0))^count).bits=
      Function.update (Function.update store (w 13) []) (w 1) (Encoding.value (store (w 0))^count).bits := by
    funext r
    by_cases e1 : r=w 1
    · subst r;simp
    · simp [initialized,Function.update_apply,e1]
  rw [final] at ran
  exact ⟨1+1+time,by omega,pushing.sequence ran⟩

end Counting.StackMachine.NaturalPower
