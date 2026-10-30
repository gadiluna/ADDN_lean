import Counting.StackMachineTestRun

namespace Counting.StackMachine.TestLazy

abbrev Code (program : Program) := Instruction (program.extraRegisters+2) (program.states+1)
abbrev Cache (program : Program) := Array (Option (Code program))

def Valid (program : Program) (cache : Cache program) : Prop :=
  ∀ control instruction,cache[control.val]?=some (some instruction) → instruction=program.code control

def empty (program : Program) : Cache program := Array.replicate (program.states+1) none

theorem empty_valid (program : Program) : Valid program (empty program) := by
  intro control instruction found
  simp [empty,Array.getElem?_replicate] at found

def lookup (program : Program) (cache : Cache program) (control : Control program) : Code program×Cache program :=
  match cache[control.val]? with
  | some (some instruction) => (instruction,cache)
  | _ => let instruction := program.code control
         (instruction,cache.setIfInBounds control.val (some instruction))

theorem lookup_correct (program : Program) (cache : Cache program) (valid : Valid program cache)
    (control : Control program) :
    (lookup program cache control).1=program.code control ∧ Valid program (lookup program cache control).2 := by
  have inserted : Valid program (cache.setIfInBounds control.val (some (program.code control))) := by
    intro other instruction found
    by_cases same : control.val=other.val
    · have equal : control=other := Fin.ext same
      subst other
      simp only [Array.getElem?_setIfInBounds_self] at found
      split at found
      · exact (Option.some.inj (Option.some.inj found)).symm
      · simp at found
    · rw [Array.getElem?_setIfInBounds_ne same] at found
      exact valid other instruction found
  unfold lookup
  split
  · rename_i instruction found
    exact ⟨valid control instruction found,valid⟩
  · exact ⟨rfl,inserted⟩

def memoStep (program : Program) (cache : Cache program) (config : Config program) :
    Option (Config program)×Cache program :=
  let (instruction,nextCache) := lookup program cache config.control
  ((match instruction with
    | .halt => none
    | .jump next => some {config with control := next}
    | .push register bit next => some ⟨next,Function.update config.store register (bit::config.store register)⟩
    | .pop register vacant zero one => match config.store register with
      | [] => some {config with control := vacant}
      | bit::rest => some ⟨if bit then one else zero,Function.update config.store register rest⟩),nextCache)

theorem memoStep_correct (program : Program) (cache : Cache program) (valid : Valid program cache) (config : Config program) :
    (memoStep program cache config).1=step program config ∧ Valid program (memoStep program cache config).2 := by
  obtain ⟨same,next⟩ := lookup_correct program cache valid config.control
  exact ⟨by simp only [memoStep,step,same];rfl,next⟩

/-- Memoization avoids eagerly evaluating code in unvisited branches. The
register refresh and cached instruction are both proved semantically exact. -/
def finishWithin (program : Program) : Nat → Nat → Cache program → Config program → Option (Nat×Config program)
  | 0,_,_,_ => none
  | fuel+1,elapsed,cache,config =>
    let (next,nextCache) := memoStep program cache config
    match next with
    | none => some (elapsed,config)
    | some next => finishWithin program fuel (elapsed+1) nextCache (TestRun.materialize next)

theorem finishWithin_sound (program : Program) (fuel start : Nat) (cache : Cache program)
    (config : Config program) (time : Nat) (output : Config program) (valid : Valid program cache)
    (finished : finishWithin program fuel start cache config=some (time,output)) :
    ∃ count,time=start+count ∧ Machine.run (step program) count config=some output ∧ step program output=none := by
  induction fuel generalizing start cache config with
  | zero => simp [finishWithin] at finished
  | succ fuel ih =>
    obtain ⟨same,nextValid⟩ := memoStep_correct program cache valid config
    change (match (memoStep program cache config).1 with
      | none => some (start,config)
      | some next => finishWithin program fuel (start+1) (memoStep program cache config).2 (TestRun.materialize next))=
        some (time,output) at finished
    cases transition : (memoStep program cache config).1 with
    | none =>
      rw [transition] at finished
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj finished)
      exact ⟨0,by omega,rfl,same.symm.trans transition⟩
    | some next =>
      simp only [transition,TestRun.materialize_eq] at finished
      obtain ⟨count,equal,ran,halted⟩ := ih (start+1) (memoStep program cache config).2 next nextValid finished
      refine ⟨count+1,by omega,?_,halted⟩
      simp only [Machine.run,←same,transition,Option.bind_some]
      exact ran

theorem initial_finished (program : Program) (input : List Bool) (fuel time : Nat) (output : Config program)
    (finished : finishWithin program fuel 0 (empty program) (initial program input)=some (time,output)) :
    HaltsAt program input time output := by
  obtain ⟨count,equal,ran,halted⟩ := finishWithin_sound program fuel 0 (empty program)
    (initial program input) time output (empty_valid program) finished
  simp only [Nat.zero_add] at equal
  exact equal.symm ▸ ⟨ran,halted⟩

end Counting.StackMachine.TestLazy
