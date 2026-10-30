import Counting.StackBinaryGcdBody
import Counting.BinaryEuclidIterations

namespace Counting.StackMachine.Binary.Gcd
open Routine

/-- Explicit finite repetition. The unary loop counter is computed from
input bit lengths, and it is independent of the magnitudes of the integers. -/
theorem gcd_loop_executes (counter : List Bool) (first second : Nat) :
    ∃ transitions ≤ 252*counter.length*(first.size+second.size+1)^2+1,
      Executes routine (file counter first second) transitions
        (file [] (euclidIter counter.length first second).1 (euclidIter counter.length first second).2) := by
  induction counter generalizing first second with
  | nil =>
      obtain ⟨executed,halted⟩ := repeat_empty 0 body (file [] first second) rfl
      exact ⟨1,by simp,⟨1,file [] first second⟩,executed,halted,rfl⟩
  | cons bit rest ih =>
      let nextFirst := if second=0 then first else second
      let nextSecond := if second=0 then second else first%second
      obtain ⟨bodyTime,bodyBound,middle,bodyRun,bodyHalt,bodyStore⟩ := body_executes rest first second
      have consumed : Function.update (file (bit::rest) first second) 0 rest = file rest first second := by
        funext r
        fin_cases r <;> rfl
      have firstRun := repeat_iteration 0 body (file (bit::rest) first second) bit rest rfl bodyTime middle
        (by simpa only [consumed] using bodyRun) bodyHalt
      have changed : middle.store = file rest nextFirst nextSecond := by
        rw [bodyStore]
        by_cases zero : second=0 <;> simp only [nextFirst,nextSecond,zero,ite_true,ite_false]
      obtain ⟨tailTime,tailBound,finish,tailRun,tailHalt,tailStore⟩ := ih nextFirst nextSecond
      have sizeBound : nextFirst.size+nextSecond.size ≤ first.size+second.size := by
        by_cases zero : second=0
        · simp only [nextFirst,nextSecond,if_pos zero]
          exact le_rfl
        · have smaller := Nat.size_le_size (Nat.mod_le first second)
          simp only [nextFirst,nextSecond,if_neg zero]
          omega
      have square : (nextFirst.size+nextSecond.size+1)^2 ≤ (first.size+second.size+1)^2 :=
        Nat.pow_le_pow_left (by omega) 2
      have tailCost := Nat.mul_le_mul_left (252*rest.length) square
      have positive : 1 ≤ (first.size+second.size+1)^2 := Nat.one_le_pow 2 _ (by omega)
      refine ⟨bodyTime+2+tailTime,?_,finish,?_,tailHalt,?_⟩
      · simp only [List.length_cons]
        nlinarith
      · rw [Machine.run_add,firstRun,Option.bind_some,changed]
        exact tailRun
      · rw [tailStore]
        simp only [List.length_cons,euclidIter_succ]
        by_cases zero : second=0 <;> simp only [nextFirst,nextSecond,zero,ite_true,ite_false]

/-- The proved logarithmic Euclidean iteration bound fixes the concrete
unary counter length needed by this implementation. -/
theorem gcd_payloads (first second : Nat) :
    ∃ transitions ≤ 252*(2*second.size+1)*(first.size+second.size+1)^2+1,
      Executes routine (file (List.replicate (2*second.size+1) true) first second) transitions
        (file [] (Nat.gcd first second) 0) := by
  simpa only [List.length_replicate,euclidIter_size_bound] using
    gcd_loop_executes (List.replicate (2*second.size+1) true) first second

end Counting.StackMachine.Binary.Gcd
