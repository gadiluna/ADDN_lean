import Counting.StackCompilerInitialization
import Counting.MachineStackBootstrap
import Counting.MachineComposition

namespace Counting.StackMachine.Compiler
open Machine

def bootMachine (program : StackMachine.Program) : Machine.Program :=
  Machine.compose (StackBootstrap.program (Registers program)) (machine program)

/-- Start from the genuine binary input tape, construct every stack block,
then simulate a complete halted stack computation. The final tape still
contains the register representation; cleanup is a separate physical phase. -/
theorem boot_halts {program : StackMachine.Program} {input : List Bool} {steps : Nat}
    {last : StackMachine.Config program} (halted : StackMachine.HaltsAt program input steps last) :
    ∃ time output,
      time ≤ 2*input.length+3*(Registers program)+6 +
        10*steps*(input.length+program.extraRegisters+steps+4) ∧
      Machine.HaltsAt (bootMachine program) input time output ∧
      output.tape.denotes = (Tape.ofWord last.encoded).denotes := by
  let boot := StackBootstrap.program (Registers program)
  let initialOutput := StackBootstrap.output (Registers program) input
  let source : Machine.Config (machine program) := ⟨0,initialOutput.tape⟩
  have same : source.denotes = (physical (StackMachine.initial program input)).denotes := by
    rw [physical_initial]
    change (⟨0, initialOutput.tape.denotes⟩ : Turing.TM0.Cfg Symbol (Machine.Control (machine program))) =
      ⟨0, (Tape.ofWord (.mark :: (input.map bitSymbol ++ List.replicate (Registers program) .separator))).denotes⟩
    rw [Tape.denotes_ofWord, StackBootstrap.bootstrap_tape]
  obtain ⟨elapsed,finish,bounded,executed,finalTape⟩ := physical_run (StackMachine.initial program input) last
    source same steps halted.1
  have finishHalted : Machine.step (machine program) finish = none :=
    halt_transport finalTape.symm (physical_halted last halted.2)
  refine ⟨(2*input.length+3*(Registers program)+5)+1+elapsed,
    secondConfig boot (machine program) finish,?_,⟨?_,?_⟩,?_⟩
  · simp only [encoded_length, initial_dataLength] at bounded
    have normalized : elapsed ≤ 10*steps*(input.length+program.extraRegisters+steps+4) := by
      convert bounded using 1; ring
    omega
  · change run (Machine.step (Machine.compose boot (machine program))) _
      (firstConfig boot (machine program) (Machine.initial boot input)) = _
    rw [show 2*input.length+3*(Registers program)+5+1+elapsed =
      (2*input.length+3*(Registers program)+5)+(elapsed+1) by omega, run_add,
      first_run _ (StackBootstrap.bootstrap_run (Registers program) input), Option.bind_some,
      run, first_halt (StackBootstrap.bootstrap_halted (Registers program) input), Option.bind_some,
      second_run, executed]
    rfl
  · change Machine.step (Machine.compose boot (machine program)) (secondConfig boot (machine program) finish) = none
    rw [second_step, finishHalted]
    rfl
  · exact congrArg Turing.TM0.Cfg.Tape finalTape

end Counting.StackMachine.Compiler
