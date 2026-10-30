import Counting.StackMachineTestRun

namespace Counting.StackMachine.TestRun

/-- Compute the finite instruction table once for regression execution. -/
def tabulate (program : Program) : Program :=
  let code := Array.ofFn program.code
  { extraRegisters := program.extraRegisters
    states := program.states
    code := fun control => code[control.val]'(by simpa only [code,Array.size_ofFn] using control.isLt) }

theorem tabulate_eq (program : Program) : tabulate program=program := by
  have code : (tabulate program).code=program.code := by
    funext control
    simp [tabulate]
  cases program with
  | mk extra states original =>
      change Program.mk extra states (tabulate (Program.mk extra states original)).code=Program.mk extra states original
      rw [code]

end Counting.StackMachine.TestRun
