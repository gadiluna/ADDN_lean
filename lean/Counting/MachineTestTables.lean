import Counting.MachineModel

namespace Counting.Machine.TestTables

/-- Materialize the finite transition table for test execution. This does not
change the abstract machine or the number of its physical transitions. -/
def symbols : Fin 5 → Symbol := ![.blank,.zero,.one,.separator,.mark]
def symbolIndex : Symbol → Fin 5
  | .blank => 0 | .zero => 1 | .one => 2 | .separator => 3 | .mark => 4

def tabulate (program : Program) : Program :=
  let table := Array.ofFn (fun control : Control program =>
    Array.ofFn (fun symbol : Fin 5 => program.code control (symbols symbol)))
  { states := program.states
    code := fun control symbol =>
      ((table[control.val]?.getD #[])[(symbolIndex symbol).val]?).getD none
    accept := program.accept }

theorem tabulate_code (program : Program) (control : Control program) (symbol : Symbol) :
    (tabulate program).code control symbol = program.code control symbol := by
  have bounded : control.val ≤ program.states := Nat.le_of_lt_succ control.isLt
  cases symbol <;> simp [tabulate,symbolIndex,symbols,bounded]

theorem tabulate_eq (program : Program) : tabulate program = program := by
  have code : (tabulate program).code = program.code := by
    funext control symbol
    exact tabulate_code program control symbol
  cases program with
  | mk states original accept =>
    change Program.mk states (tabulate (Program.mk states original accept)).code accept = _
    rw [code]

end Counting.Machine.TestTables
