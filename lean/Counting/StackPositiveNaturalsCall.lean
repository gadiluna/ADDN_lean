import Counting.StackRationalPositiveIntegral
import Counting.StackRoutineClean
import Counting.StackRegisterFrames

namespace Counting.StackMachine.PositiveNaturalsCall
open Routine

/-- The two public fields survive the sixteen-register scalar transducer;
all private cells are explicitly cleared before returning. -/
def file (input output privateInput privateOutput : List Bool) : Fin 20 → List Bool :=
  ![input,output,[],[],privateInput,privateOutput,[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
def addresses : Fin 16 ↪ Fin 20 := ⟨fun r => ⟨r.val+4,by omega⟩,
  by intro a b equal; apply Fin.ext; have := congrArg (fun r : Fin 20 => r.val) equal; dsimp at this; omega⟩
abbrev invoke (scalar : Routine 14) : Routine 18 :=
  sequence (ofProgram (ListPrograms.copyProgram 17 0 4 2))
    (sequence (relocate (isolate scalar) addresses) (move 17 5 1 2))

theorem invoke_executes (scalar : Routine 14) (function : List Bool → List Bool)
    (bound : Nat → Nat) (computes : ComputesIn scalar.program function bound) (input : List Bool) :
    ∃ time ≤ 30*(bound input.length+input.length+3),
      Executes (invoke scalar) (file input [] [] []) time (file input (function input) [] []) := by
  have copied := copy_executes 17 0 4 2 (by decide) (by decide) (by decide) (file input [] [] []) rfl
  have copiedStore : Function.update (file input [] [] []) 4 (input++[]) = file input [] input [] := by
    funext r; fin_cases r <;> simp [file]
  change Executes _ _ (5*input.length+2) (Function.update (file input [] [] []) 4 (input++[])) at copied
  rw [copiedStore] at copied
  obtain ⟨time,bounded,ran⟩ := isolate_executes scalar function bound computes input
  have called : Executes (relocate (isolate scalar) addresses) (file input [] input []) time (file input [] [] (function input)) := by
    apply relocate_executes_frame (isolate scalar) addresses _ _ _ _ time _ _ _ ran
    · funext r; fin_cases r <;> simp [file,addresses,inputStore]
    · intro r; fin_cases r <;> simp [file,addresses,outputStore]
    · intro r outside
      fin_cases r
      · simp [file]
      · simp [file]
      · simp [file]
      · simp [file]
      · exact False.elim (outside 0 rfl)
      · exact False.elim (outside 1 rfl)
      all_goals simp [file]
  have moved := move_executes 17 5 1 2 (by decide) (by decide) (by decide) (file input [] [] (function input)) rfl
  have movedStore : Function.update (Function.update (file input [] [] (function input)) 1 (function input++[])) 5 [] =
      file input (function input) [] [] := by
    funext r; fin_cases r <;> simp [file]
  change Executes _ _ (6*(function input).length+4)
    (Function.update (Function.update (file input [] [] (function input)) 1 (function input++[])) 5 []) at moved
  rw [movedStore] at moved
  refine ⟨_,?_,copied.sequence (called.sequence moved)⟩
  have length := computed_length_le scalar function bound computes input
  change time ≤ 17*(bound input.length+input.length+3) at bounded
  omega

abbrev test := invoke RationalArithmetic.Predicates.positiveIntegralRoutine
abbrev extract := invoke RationalArithmetic.numeratorToNatRoutine

theorem test_executes (input : List Bool) :
    ∃ time ≤ 2000*(input.length+1),
      Executes test (file input [] [] []) time
        (file input [RationalArithmetic.Predicates.positiveIntegralPredicate input] [] []) := by
  obtain ⟨time,bounded,ran⟩ := invoke_executes RationalArithmetic.Predicates.positiveIntegralRoutine
    _ _ RationalArithmetic.Predicates.positiveIntegral_computes input
  refine ⟨time,bounded.trans ?_,ran⟩
  simp only [Complexity.polynomial,pow_one]
  omega

theorem extract_executes (input : List Bool) :
    ∃ time ≤ 2000*(input.length+1),
      Executes extract (file input [] [] []) time
        (file input (Encoding.natural.encode (RationalArithmetic.numeratorNatural input)) [] []) := by
  obtain ⟨time,bounded,ran⟩ := invoke_executes RationalArithmetic.numeratorToNatRoutine
    _ _ RationalArithmetic.numeratorToNat_computes input
  refine ⟨time,bounded.trans ?_,ran⟩
  simp only [Complexity.polynomial,pow_one]
  omega

end Counting.StackMachine.PositiveNaturalsCall
