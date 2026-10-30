import Counting.StackCompilerBoot
import Counting.StackCompilerOutput
import Counting.MachineStackCleanup

/-! A complete compiler from the bit-stack language to the fixed-alphabet
Turing model. Bootstrap, simulation, and cleanup are all executed and
charged. In particular the output contract is the entire clean tape. -/
namespace Counting.StackMachine.Compiler
open Machine

def compile (program : StackMachine.Program) : Machine.Program :=
  Machine.compose (bootMachine program) StackCleanup.program

theorem cleanup_config (config : StackMachine.Config program) :
    ∃ elapsed output, elapsed ≤ 3*config.encoded.length+1 ∧
      run (Machine.step StackCleanup.program) elapsed
        ⟨0,Tape.ofWord config.encoded⟩ = some output ∧
      Machine.step StackCleanup.program output = none ∧
      output.tape.denotes = Turing.Tape.mk₁ ((config.store 1).map bitSymbol) := by
  refine ⟨2*(config.store 0).length+2*(config.store 1).length+3*(after config.store 1).length+10,
    StackCleanup.result (config.store 0) (config.store 1) (after config.store 1),?_,?_,
    StackCleanup.cleanup_halted _ _ _,StackCleanup.cleanup_tape _ _ _⟩
  · rw [encoded_output]
    exact StackCleanup.cleanup_steps_le _ _ _
  · rw [encoded_output]
    exact StackCleanup.cleanup_run _ _ _ (blocks_ne_blank _)

/-- A halted stack run yields a halted physical transduction with a clean
tape. The quadratic simulation bound includes every auxiliary phase. -/
theorem compile_halts {program : StackMachine.Program} {input : List Bool} {steps : Nat}
    {last : StackMachine.Config program} (halted : StackMachine.HaltsAt program input steps last) :
    ∃ time output, time ≤ 20*(input.length+program.extraRegisters+steps+4)^2 ∧
      Machine.HaltsAt (compile program) input time output ∧
      output.tape.denotes = Turing.Tape.mk₁ ((last.store 1).map bitSymbol) := by
  obtain ⟨firstTime,firstOutput,firstBound,firstHalts,firstTape⟩ := boot_halts halted
  obtain ⟨lastTime,lastOutput,lastBound,lastRun,lastHalt,lastTape⟩ := cleanup_config last
  let source : Machine.Config StackCleanup.program := ⟨0,firstOutput.tape⟩
  have same : (⟨0,Tape.ofWord last.encoded⟩ : Machine.Config StackCleanup.program).denotes = source.denotes := by
    change (⟨0,(Tape.ofWord last.encoded).denotes⟩ : Turing.TM0.Cfg Symbol (Machine.Control StackCleanup.program)) =
      ⟨0,firstOutput.tape.denotes⟩
    rw [firstTape]
  obtain ⟨finish,executed,finalTape⟩ := run_transport StackCleanup.program lastTime
    ⟨0,Tape.ofWord last.encoded⟩ source lastOutput same lastRun
  have finishHalt : Machine.step StackCleanup.program finish = none := halt_transport finalTape.symm lastHalt
  have size : last.encoded.length ≤ input.length+program.extraRegisters+steps+3 := by
    have data := run_dataLength (StackMachine.initial program input) last steps halted.1
    rw [initial_dataLength] at data
    rw [encoded_length]
    omega
  refine ⟨firstTime+1+lastTime,secondConfig (bootMachine program) StackCleanup.program finish,
    ?_,⟨?_,?_⟩,?_⟩
  · dsimp [Registers] at firstBound
    have bound := Nat.mul_le_mul_left 3 size
    nlinarith [sq_nonneg (input.length+program.extraRegisters+steps+4 : Int)]
  · change run (Machine.step (Machine.compose (bootMachine program) StackCleanup.program)) _
      (firstConfig (bootMachine program) StackCleanup.program (Machine.initial (bootMachine program) input)) = _
    rw [show firstTime+1+lastTime = firstTime+(lastTime+1) by omega,run_add,
      first_run _ firstHalts.1,Option.bind_some,run,first_halt firstHalts.2,Option.bind_some,
      second_run,executed]
    rfl
  · change Machine.step (Machine.compose (bootMachine program) StackCleanup.program)
      (secondConfig (bootMachine program) StackCleanup.program finish) = none
    rw [second_step,finishHalt]
    rfl
  · exact (congrArg Turing.TM0.Cfg.Tape finalTape).trans lastTape

/-- Compilation preserves executable transductions and charges the physical
cost of a stack run bounded by an arbitrary function. -/
theorem computesCleanIn {program : StackMachine.Program} {function : List Bool → List Bool}
    {bound : Nat → Nat} (computes : StackMachine.ComputesIn program function bound) :
    Complexity.ComputesCleanIn (compile program) function
      (fun length => 20*(length+program.extraRegisters+bound length+4)^2) := by
  intro input
  obtain ⟨steps,last,bounded,halted,value⟩ := computes input
  obtain ⟨time,output,cost,physicalHalts,tape⟩ := compile_halts halted
  refine ⟨time,output,?_,physicalHalts,?_⟩
  · exact cost.trans (Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left (by omega) 2))
  · rw [value] at tape
    exact tape

/-- A polynomial stack-step bound gives a polynomial true Turing bound;
this is not an assertion that arbitrary Lean functions have such a program. -/
theorem computesCleanIn_polynomial {program : StackMachine.Program} {function : List Bool → List Bool}
    (coefficient exponent : Nat)
    (computes : StackMachine.ComputesIn program function (Complexity.polynomial coefficient exponent)) :
    Complexity.ComputesCleanIn (compile program) function
      (Complexity.polynomial (20*(coefficient+program.extraRegisters+5)^2) (2*(exponent+1))) := by
  have physicalComputes := computesCleanIn computes
  intro input
  obtain ⟨steps,output,bounded,halted,tape⟩ := physicalComputes input
  refine ⟨steps,output,?_,halted,tape⟩
  apply bounded.trans
  have positive : 1 ≤ input.length+1 := by omega
  have power : 1 ≤ (input.length+1)^exponent := Nat.one_le_pow exponent _ positive
  have lengthBound : input.length ≤ (input.length+1)^(exponent+1) := by
    calc
      input.length ≤ input.length+1 := by omega
      _ ≤ (input.length+1)^(exponent+1) := by
        rw [pow_succ]
        nlinarith
  have powerBound : (input.length+1)^exponent ≤ (input.length+1)^(exponent+1) := by
    rw [pow_succ]
    nlinarith
  have baseBound : input.length+program.extraRegisters+Complexity.polynomial coefficient exponent input.length+4 ≤
      (coefficient+program.extraRegisters+5)*(input.length+1)^(exponent+1) := by
    dsimp [Complexity.polynomial]
    nlinarith
  calc
    _ ≤ 20*((coefficient+program.extraRegisters+5)*(input.length+1)^(exponent+1))^2 :=
      Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left baseBound 2)
    _ = _ := by simp only [Complexity.polynomial, mul_pow, ← pow_mul]; ring

end Counting.StackMachine.Compiler
