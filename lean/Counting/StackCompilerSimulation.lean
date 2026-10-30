import Counting.StackCompilerPop

/-! Every stack transition has a physical implementation. The bound is on
actual single-cell moves/writes; it includes scans, shifts, and returns. -/
namespace Counting.StackMachine.Compiler
open Machine

theorem instruction_run {program : StackMachine.Program} (first last : StackMachine.Config program)
    (success : StackMachine.step program first = some last) :
    ∃ steps padding, steps ≤ 10*(first.encoded.length+1) ∧
      run (transition program) steps (atEntry first) = some (paddedEntry last padding) := by
  unfold StackMachine.step at success
  cases instruction : program.code first.control with
  | halt => simp [instruction] at success
  | jump next =>
      simp only [instruction, Option.some.injEq] at success
      subst last
      refine ⟨1,0,by omega,?_⟩
      simp only [run, transition, FiniteControl.step, atEntry, entry, code, instruction,
        Option.map_some, Option.bind_some, paddedEntry, StackMachine.Config.encoded,
        Tape.ofWord, List.headD_cons, List.tail_cons, List.replicate_zero, List.append_nil, Tape.write]
  | push register bit next =>
      simp only [instruction, Option.some.injEq] at success
      subst last
      refine ⟨_,1,?_,push_run first register bit next instruction⟩
      have size := split_length_bound first register
      simp only [List.length_append, List.length_cons] at size ⊢
      omega
  | pop register empty zero one =>
      cases contents : first.store register with
      | nil =>
          simp only [instruction, contents, Option.some.injEq] at success
          subst last
          refine ⟨_,0,?_,pop_empty_run first register empty zero one instruction contents⟩
          have size := split_length_bound first register
          omega
      | cons bit rest =>
          simp only [instruction, contents, Option.some.injEq] at success
          subst last
          refine ⟨_,2,?_,pop_bit_run first register empty zero one bit rest instruction contents⟩
          have size := split_length_bound first register
          simp only [contents, block_length, List.length_cons, List.length_append, List.length_nil] at size ⊢
          omega

def physical {program : StackMachine.Program} (config : StackMachine.Config program) : Machine.Config (machine program) :=
  FiniteControl.config (encode program) (code program) (fun _ => true) (atEntry config)

theorem physical_step {program : StackMachine.Program} (first last : StackMachine.Config program)
    (success : StackMachine.step program first = some last) :
    ∃ steps output, steps ≤ 10*(first.encoded.length+1) ∧
      run (Machine.step (machine program)) steps (physical first) = some output ∧
      output.denotes = (physical last).denotes := by
  obtain ⟨steps,padding,bounded,executed⟩ := instruction_run first last success
  refine ⟨steps,FiniteControl.config (encode program) (code program) (fun _ => true) (paddedEntry last padding),
    bounded,?_,?_⟩
  · rw [physical, compiled_run, executed]
    rfl
  · change (⟨(encode program) (entry last.control), (paddedEntry last padding).tape.denotes⟩ :
      Turing.TM0.Cfg Symbol (Machine.Control (machine program))) =
      ⟨(encode program) (entry last.control), (atEntry last).tape.denotes⟩
    rw [paddedEntry_tape]

theorem physical_step_transport {program : StackMachine.Program} (first last : StackMachine.Config program)
    (source : Machine.Config (machine program)) (same : source.denotes = (physical first).denotes)
    (success : StackMachine.step program first = some last) :
    ∃ steps output, steps ≤ 10*(first.encoded.length+1) ∧
      run (Machine.step (machine program)) steps source = some output ∧
      output.denotes = (physical last).denotes := by
  obtain ⟨steps,output,bounded,executed,final⟩ := physical_step first last success
  obtain ⟨result,ran,tape⟩ := run_transport (machine program) steps (physical first) source output same.symm executed
  exact ⟨steps,result,bounded,ran,tape.trans final⟩

theorem physical_run {program : StackMachine.Program} (first last : StackMachine.Config program)
    (source : Machine.Config (machine program)) (same : source.denotes = (physical first).denotes)
    (steps : Nat) (success : run (StackMachine.step program) steps first = some last) :
    ∃ time output, time ≤ 10*steps*(first.encoded.length+steps+1) ∧
      run (Machine.step (machine program)) time source = some output ∧
      output.denotes = (physical last).denotes := by
  induction steps generalizing first source with
  | zero =>
      have equal := Option.some.inj success
      subst last
      exact ⟨0,source,by omega,rfl,same⟩
  | succ steps ih =>
      cases transition : StackMachine.step program first with
      | none => simp only [run, transition, Option.bind_none] at success; contradiction
      | some middle =>
          have tail : run (StackMachine.step program) steps middle = some last := by
            simpa only [run, transition, Option.bind_some] using success
          obtain ⟨firstTime,next,firstBound,firstRun,nextTape⟩ := physical_step_transport first middle source same transition
          obtain ⟨restTime,output,restBound,restRun,finalTape⟩ := ih middle next nextTape tail
          have size : middle.encoded.length ≤ first.encoded.length+1 := by
            have bound := step_dataLength first middle transition
            simp only [encoded_length]
            omega
          refine ⟨firstTime+restTime,output,?_,?_,finalTape⟩
          · nlinarith
          · rw [run_add,firstRun,Option.bind_some,restRun]

theorem physical_halted {program : StackMachine.Program} (config : StackMachine.Config program)
    (halted : StackMachine.step program config = none) :
    Machine.step (machine program) (physical config) = none := by
  have simulated := FiniteControl.step_compile (encode program) (code program) (fun _ => true) (atEntry config)
  have stopped : FiniteControl.step (code program) (atEntry config) = none := entry_halted config halted
  rw [stopped] at simulated
  exact simulated

end Counting.StackMachine.Compiler
