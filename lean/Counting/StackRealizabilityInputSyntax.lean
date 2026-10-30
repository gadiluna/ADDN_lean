import Counting.StackRealizabilityInputComponents
import Counting.StackEncodingDagMachine
import Counting.StackRoutineClean

namespace Counting.StackMachine.RealizabilityCheck
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def inputSyntaxStore (input flags : List Bool) : Store 98 :=
  fun r=>if r=79 then input else if r=85 then flags else []

def inputSyntaxStart (input : List Bool) : Store 98 :=
  Function.update (inputSyntaxStore input []) 70 input

def inputSyntax : Routine 98 :=
  mapRegisters componentRoles (isolate DagParser.verifierInput.recognition)

/-- Total syntax gate for the exact verifier tuple, on every binary word.
The preserved backup is explicit; all parser output and scratch are erased
before the semantic branch is selected. -/
theorem inputSyntax_executes (input : List Bool) :
    ∃ time ≤ 106000*(input.length+1)^4,
      Executes inputSyntax (inputSyntaxStart input) time
        (inputSyntaxStore input [(Encoding.verifierInput.decodeExact input).isSome]) := by
  have computes : ComputesIn DagParser.verifierInput.recognition.program
      (fun input=>[(Encoding.verifierInput.decodeExact input).isSome])
      (Complexity.polynomial 5853 4) := DagParser.verifierInput.recognition_computes
  obtain ⟨time,bound,run⟩ := isolate_executes DagParser.verifierInput.recognition _ _ computes input
  refine ⟨time,?_,?_⟩
  · change time ≤ 18*(5853*(input.length+1)^4+input.length+3) at bound
    have linear := Nat.le_self_pow (by decide : 4≠0) (input.length+1)
    have one := Nat.one_le_pow 4 (input.length+1) (by omega)
    omega
  · apply relocate_executes_frame (isolate DagParser.verifierInput.recognition) componentRoles
      (inputSyntaxStart input) (inputSyntaxStore input [(Encoding.verifierInput.decodeExact input).isSome])
      (inputStore 15 input) (outputStore 15 [(Encoding.verifierInput.decodeExact input).isSome]) time _ _ _ run
    · funext i
      fin_cases i <;> simp [inputSyntaxStart,inputSyntaxStore,inputStore,componentRoles]
    · intro i
      fin_cases i <;> simp [inputSyntaxStore,outputStore,componentRoles]
    · intro i outside
      have n70:i≠70 := by intro same;subst i;exact outside 0 rfl
      have n85:i≠85 := by intro same;subst i;exact outside 1 rfl
      simp [inputSyntaxStart,inputSyntaxStore,n70,n85]

end Counting.StackMachine.RealizabilityCheck
