import Counting.ComplexityModel

/-! An actual finite-control simulation on alternate physical tape cells.
Every original write or movement is simulated by exactly two transitions;
intervening cells are ignored. This supports verification of framed input
without assuming a free decoding operation. -/
namespace Counting.Machine

def skipPairs : List Symbol → List Symbol
  | _ :: payload :: rest => payload :: skipPairs rest
  | _ => []

def Tape.unstride (tape : Tape) : Tape :=
  ⟨skipPairs tape.left, tape.head, skipPairs tape.right⟩

theorem Tape.unstride_write (tape : Tape) (symbol : Symbol) :
    (tape.write symbol).unstride = tape.unstride.write symbol := rfl

theorem Tape.unstride_move_twice (tape : Tape) (direction : Turing.Dir) :
    ((tape.move direction).move direction).unstride = tape.unstride.move direction := by
  rcases tape with ⟨left, head, right⟩
  cases direction with
  | left => cases left with
    | nil => rfl
    | cons first rest => cases rest <;> rfl
  | right => cases right with
    | nil => rfl
    | cons first rest => cases rest <;> rfl

def strideControl (program : Program) (phase : Fin 4) (control : Control program) :
    Fin (4 * (program.states + 1)) :=
  ⟨phase.val * (program.states + 1) + control.val, by have := phase.isLt; have := control.isLt; nlinarith⟩

def strideProgram (program : Program) : Program where
  states := 4 * program.states + 3
  code control symbol :=
    let original : Control program := ⟨control.val % (program.states + 1), Nat.mod_lt _ (by omega)⟩
    match control.val / (program.states + 1) with
    | 0 => (program.code original symbol).map (fun (next, action) =>
        match action with
        | .write value => (strideControl program 3 next, .write value)
        | .move .left => (strideControl program 1 next, .move .left)
        | .move .right => (strideControl program 2 next, .move .right))
    | 1 => some (strideControl program 0 original, .move .left)
    | 2 => some (strideControl program 0 original, .move .right)
    | _ => some (strideControl program 0 original, .write symbol)
  accept control :=
    control.val < program.states + 1 &&
      program.accept ⟨control.val % (program.states + 1), Nat.mod_lt _ (by omega)⟩

theorem strideControl_mod (program : Program) (phase : Fin 4) (control : Control program) :
    (strideControl program phase control).val % (program.states + 1) = control.val := by
  simp only [strideControl, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt control.isLt]

theorem strideControl_div (program : Program) (phase : Fin 4) (control : Control program) :
    (strideControl program phase control).val / (program.states + 1) = phase.val := by
  dsimp only [strideControl]
  rw [Nat.mul_comm phase.val, Nat.mul_add_div (by omega), Nat.div_eq_of_lt control.isLt, Nat.add_zero]

def strideConfig (program : Program) (control : Control program) (tape : Tape) :
    Config (strideProgram program) := ⟨strideControl program 0 control, tape⟩

theorem stride_step (program : Program) (control next : Control program) (tape : Tape)
    (action : Turing.TM0.Stmt Symbol)
    (instruction : program.code control tape.head = some (next, action)) :
    ∃ nextTape, run (step (strideProgram program)) 2 (strideConfig program control tape) =
        some (strideConfig program next nextTape) ∧
      nextTape.unstride = match action with
        | .write symbol => tape.unstride.write symbol
        | .move direction => tape.unstride.move direction := by
  cases action with
  | write symbol =>
      refine ⟨tape.write symbol, ?_, rfl⟩
      simp [run, step, strideConfig, strideProgram, strideControl_mod, strideControl_div,
        instruction, Tape.write]
  | move direction =>
      refine ⟨(tape.move direction).move direction, ?_, Tape.unstride_move_twice tape direction⟩
      cases direction <;>
        simp [run, step, strideConfig, strideProgram, strideControl_mod, strideControl_div, instruction]

theorem stride_halt (program : Program) (control : Control program) (tape : Tape)
    (halted : program.code control tape.head = none) :
    step (strideProgram program) (strideConfig program control tape) = none := by
  simp [step, strideConfig, strideProgram, strideControl_mod, strideControl_div, halted]

theorem stride_accept (program : Program) (control : Control program) (tape : Tape) :
    (strideProgram program).accept (strideConfig program control tape).control = program.accept control := by
  simp [strideConfig, strideProgram, strideControl, Nat.mod_eq_of_lt control.isLt, control.isLt]

theorem stride_step_simulates (program : Program) (control : Control program) (tape : Tape)
    (next : Config program) (success : step program ⟨control, tape.unstride⟩ = some next) :
    ∃ nextTape, run (step (strideProgram program)) 2 (strideConfig program control tape) =
        some (strideConfig program next.control nextTape) ∧ nextTape.unstride = next.tape := by
  obtain ⟨⟨nextControl, action⟩, instruction, equal⟩ := Option.map_eq_some_iff.mp success
  subst next
  cases action <;> exact stride_step program control nextControl tape _ instruction

/-- Exact two-for-one simulation for any tape with the stated decoded
configuration, including arbitrary contents in the ignored cells. -/
theorem stride_run (program : Program) (steps : Nat) (start finish : Config program) (tape : Tape)
    (decoded : tape.unstride = start.tape)
    (success : run (step program) steps start = some finish) :
    ∃ finishTape,
      run (step (strideProgram program)) (2 * steps) (strideConfig program start.control tape) =
        some (strideConfig program finish.control finishTape) ∧ finishTape.unstride = finish.tape := by
  induction steps generalizing start tape with
  | zero =>
      have equal : start = finish := Option.some.inj success
      subst finish
      exact ⟨tape, rfl, decoded⟩
  | succ steps ih =>
      cases next : step program start with
      | none => simp only [run, next, Option.bind_none] at success; contradiction
      | some middle =>
          have nextDecoded : step program ⟨start.control, tape.unstride⟩ = some middle := by
            simpa only [decoded] using next
          obtain ⟨middleTape, first, middleDecoded⟩ := stride_step_simulates program start.control tape middle nextDecoded
          have rest : run (step program) steps middle = some finish := by
            simpa only [run, next, Option.bind_some] using success
          obtain ⟨finishTape, tail, finishDecoded⟩ := ih middle middleTape middleDecoded rest
          refine ⟨finishTape, ?_, finishDecoded⟩
          rw [show 2 * (steps + 1) = 2 + 2 * steps by omega, run_add, first, Option.bind_some, tail]

theorem stride_terminal (program : Program) (finish : Config program) (tape : Tape)
    (decoded : tape.unstride = finish.tape) (halted : step program finish = none) :
    step (strideProgram program) (strideConfig program finish.control tape) = none := by
  apply stride_halt
  have code := Option.map_eq_none_iff.mp halted
  have head := congrArg Tape.head decoded
  simpa only [Tape.unstride] using head ▸ code

end Counting.Machine
