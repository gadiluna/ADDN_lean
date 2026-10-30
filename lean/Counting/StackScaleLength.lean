import Counting.StackRoutineUnary
import Counting.StackRoutineBasic

namespace Counting.StackMachine.Routine

/-- A fixed number of length measurements. This produces a scaled unary
counter without requiring the source bits themselves to be unary markers. -/
def scaleLength (extra : Nat) (source target temporary : Fin (extra+3)) : Nat → Routine (extra+1)
  | 0 => skip (extra+1)
  | multiplier+1 => sequence (scaleLength extra source target temporary multiplier)
      (ofProgram (Unary.lengthProgram extra source target temporary))

theorem scaleLength_executes (extra : Nat) (source target temporary : Fin (extra+3))
    (st : source ≠ target) (sw : source ≠ temporary) (tw : target ≠ temporary)
    (multiplier : Nat) (store : Fin (extra+3) → List Bool) (workEmpty : store temporary=[]) :
    Executes (scaleLength extra source target temporary multiplier) store
      (multiplier*(5*(store source).length+3))
      (Function.update store target (List.replicate (multiplier*(store source).length) true++store target)) := by
  induction multiplier generalizing store with
  | zero =>
      simpa only [scaleLength,Nat.zero_mul,List.replicate_zero,List.nil_append,Function.update_eq_self] using skip_executes store
  | succ multiplier ih =>
      let middle := Function.update store target (List.replicate (multiplier*(store source).length) true++store target)
      have measured := length_executes extra source target temporary st sw tw middle
        (by simp [middle,Ne.symm tw,workEmpty])
      have combined := (ih store workEmpty).sequence measured
      have cost : multiplier*(5*(store source).length+3)+1+(5*(store source).length+2) =
          (multiplier+1)*(5*(store source).length+3) := by ring
      simpa +instances only [scaleLength,Unary.lengthProgram,middle,Function.update_self,
        Function.update_of_ne st,Function.update_idem,← List.append_assoc,← List.replicate_add,cost,
        show (store source).length+multiplier*(store source).length=(multiplier+1)*(store source).length by ring] using combined

end Counting.StackMachine.Routine
