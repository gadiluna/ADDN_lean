import Counting.StackAuditCompleteBank

namespace Counting.StackMachine.AuditComplete

/-- A uniform natural polynomial majorant, with no dependence of its
coefficient or degree on the encoded input. -/
def PolyBound (function : Nat → Nat) : Prop :=
  ∃ coefficient degree,∀ size,1≤ size → function size≤ coefficient*size^degree

namespace PolyBound
theorem constant (value : Nat) : PolyBound (fun _=>value) := by
  exact ⟨value,0,by intro size _;simp⟩

theorem identity : PolyBound (fun size=>size) := by
  exact ⟨1,1,by intro size _;simp⟩

theorem add {f g : Nat → Nat} (hf : PolyBound f) (hg : PolyBound g) :
    PolyBound (fun size=>f size+g size) := by
  obtain ⟨a,d,ha⟩:=hf
  obtain ⟨b,e,hb⟩:=hg
  refine ⟨a+b,d+e,?_⟩
  intro size positive
  have first: f size≤ a*size^(d+e):=(ha size positive).trans
    (Nat.mul_le_mul_left a (Nat.pow_le_pow_right positive (by omega)))
  have second:g size≤ b*size^(d+e):=(hb size positive).trans
    (Nat.mul_le_mul_left b (Nat.pow_le_pow_right positive (by omega)))
  rw [Nat.add_mul]
  exact Nat.add_le_add first second

theorem scale {f : Nat → Nat} (hf : PolyBound f) (factor : Nat) :
    PolyBound (fun size=>factor*f size) := by
  obtain ⟨a,d,ha⟩:=hf
  refine ⟨factor*a,d,?_⟩
  intro size positive
  simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left factor (ha size positive)

theorem power {f : Nat → Nat} (hf : PolyBound f) (exponent : Nat) :
    PolyBound (fun size=>(f size)^exponent) := by
  obtain ⟨a,d,ha⟩:=hf
  refine ⟨a^exponent,d*exponent,?_⟩
  intro size positive
  simpa only [mul_pow,←pow_mul] using Nat.pow_le_pow_left (ha size positive) exponent
end PolyBound

theorem executed_output_length {extra : Nat} (routine : Routine extra) (input output : List Bool)
    (time : Nat) (run : Routine.Executes routine (Routine.inputStore extra input) time
      (Routine.outputStore extra output)) : output.length≤ input.length+time := by
  obtain ⟨finish,ran,halted,stored⟩:=run
  have growth:=run_dataLength (initial routine.program input) finish time ran
  rw [initial_dataLength] at growth
  have part:(finish.store 1).length≤ finish.dataLength :=
    Finset.single_le_sum (f:=fun i=>(finish.store i).length)
      (fun _ _=>Nat.zero_le _) (Finset.mem_univ 1)
  rw [stored] at part
  simpa [Routine.outputStore] using part.trans growth

theorem solvedValues_length (vista : Executable.Vista) (leaders anchor : Nat) :
    (AnchorSolve.resultWord vista anchor leaders).length≤
      (AnchorMatrix.inputWord anchor leaders vista).length+
        AnchorSolve.polynomialCoefficient*((AnchorMatrix.inputWord anchor leaders vista).length+1)^4500 := by
  obtain ⟨time,bounded,run⟩:=AnchorSolve.routine_executes vista anchor leaders
  have input : GaussianCalls.file (AnchorMatrix.inputWord anchor leaders vista) [] [] []=
      Routine.inputStore 54 (AnchorMatrix.inputWord anchor leaders vista) := by
    funext r;fin_cases r <;> simp [GaussianCalls.file,Routine.inputStore]
  have output : GaussianCalls.file [] (AnchorSolve.resultWord vista anchor leaders) [] []=
      Routine.outputStore 54 (AnchorSolve.resultWord vista anchor leaders) := by
    funext r;fin_cases r <;> simp [GaussianCalls.file,Routine.outputStore]
  rw [input,output] at run
  exact (executed_output_length _ _ _ _ run).trans (Nat.add_le_add_left bounded _)

theorem postSolver_output_length (vista : Executable.Vista) (candidate anchor : Nat)
    (values : Option (Array Rat)) (fits:anchor≤ vista.nodes.size) (valid:vista.valid=true) :
    (AuditPostSolver.outputWord vista candidate anchor values).length≤
      (AuditPostSolver.inputWord vista candidate anchor values).length+
        AuditPostSolver.completeCoefficient*((AuditPostSolver.inputWord vista candidate anchor values).length+1)^51 := by
  obtain ⟨time,bounded,run⟩:=AuditPostSolver.complete_polynomial vista candidate anchor values fits valid
  exact (executed_output_length _ _ _ _ run).trans (Nat.add_le_add_left bounded _)

end Counting.StackMachine.AuditComplete
