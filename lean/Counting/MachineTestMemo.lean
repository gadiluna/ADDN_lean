import Counting.MachineTestTables

namespace Counting.Machine.TestMemo
open TestTables

abbrev Transition (program : Program) := Option (Control program×Turing.TM0.Stmt Symbol)
abbrev Cache (program : Program) := Array (Option (Transition program))
def key {program : Program} (control : Control program) (symbol : Symbol) : Nat :=
  5*control.val+(symbolIndex symbol).val

def Valid (program : Program) (cache : Cache program) : Prop :=
  ∀ control symbol transition, cache[key control symbol]?=some (some transition) →
    transition=program.code control symbol

def empty (program : Program) : Cache program := Array.replicate (5*(program.states+1)) none

theorem empty_valid (program : Program) : Valid program (empty program) := by
  intro control symbol transition found
  simp [empty,Array.getElem?_replicate] at found

theorem key_injective {program : Program} {c d : Control program} {s t : Symbol}
    (equal : key c s=key d t) : c=d ∧ s=t := by
  have hs := (symbolIndex s).isLt
  have ht := (symbolIndex t).isLt
  have values : c.val=d.val ∧ (symbolIndex s).val=(symbolIndex t).val := by
    dsimp [key] at equal
    omega
  refine ⟨Fin.ext values.1,?_⟩
  cases s <;> cases t <;> simp_all [symbolIndex]

def lookup (program : Program) (cache : Cache program) (control : Control program) (symbol : Symbol) :
    Transition program×Cache program :=
  match cache[key control symbol]? with
  | some (some transition) => (transition,cache)
  | _ => let transition := program.code control symbol
         (transition,cache.setIfInBounds (key control symbol) (some transition))

theorem lookup_correct (program : Program) (cache : Cache program) (valid : Valid program cache)
    (control : Control program) (symbol : Symbol) :
    (lookup program cache control symbol).1=program.code control symbol ∧
      Valid program (lookup program cache control symbol).2 := by
  have inserted : Valid program (cache.setIfInBounds (key control symbol) (some (program.code control symbol))) := by
    intro c s transition found
    by_cases same : key control symbol=key c s
    · obtain ⟨rfl,rfl⟩ := key_injective same
      simp only [Array.getElem?_setIfInBounds_self] at found
      split at found
      · exact (Option.some.inj (Option.some.inj found)).symm
      · simp at found
    · rw [Array.getElem?_setIfInBounds_ne same] at found
      exact valid c s transition found
  unfold lookup
  split
  · rename_i transition found
    exact ⟨valid control symbol transition found,valid⟩
  · exact ⟨rfl,inserted⟩

def memoStep (program : Program) (cache : Cache program) (config : Config program) :
    Option (Config program)×Cache program :=
  let (transition,nextCache) := lookup program cache config.control config.tape.head
  (transition.map (fun (control,action) => ⟨control,match action with
    | .move direction => config.tape.move direction
    | .write symbol => config.tape.write symbol⟩),nextCache)

/-- Every memoized transition is the original physical transition; the
cache contains only values of the actual program's finite code table. -/
theorem memoStep_correct (program : Program) (cache : Cache program) (valid : Valid program cache)
    (config : Config program) :
    (memoStep program cache config).1=step program config ∧
      Valid program (memoStep program cache config).2 := by
  obtain ⟨same,next⟩ := lookup_correct program cache valid config.control config.tape.head
  refine ⟨?_,next⟩
  simp only [memoStep,step,same]
  rfl

def finishWithin (program : Program) : Nat → Nat → Cache program → Config program → Option (Nat×Config program)
  | 0,_,_,_ => none
  | fuel+1,steps,cache,config =>
    let (next,nextCache) := memoStep program cache config
    match next with
    | none => some (steps,config)
    | some next => finishWithin program fuel (steps+1) nextCache next

/-- A successful memoized test run is an exact halted run of the original
machine with precisely the reported transition count. -/
theorem finishWithin_sound (program : Program) (fuel start : Nat) (cache : Cache program)
    (config : Config program) (steps : Nat) (output : Config program)
    (valid : Valid program cache)
    (finished : finishWithin program fuel start cache config=some (steps,output)) :
    ∃ count, steps=start+count ∧ run (step program) count config=some output ∧ step program output=none := by
  induction fuel generalizing start cache config with
  | zero => simp [finishWithin] at finished
  | succ fuel ih =>
    obtain ⟨same,nextValid⟩ := memoStep_correct program cache valid config
    change (match (memoStep program cache config).1 with
      | none => some (start,config)
      | some next => finishWithin program fuel (start+1) (memoStep program cache config).2 next)=some (steps,output) at finished
    cases nextStep : (memoStep program cache config).1 with
    | none =>
      rw [nextStep] at finished
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj finished)
      exact ⟨0,by omega,rfl,same.symm.trans nextStep⟩
    | some next =>
      rw [nextStep] at finished
      obtain ⟨count,countEq,ran,halted⟩ := ih (start+1) (memoStep program cache config).2 next nextValid finished
      refine ⟨count+1,by omega,?_,halted⟩
      simp only [run,←same,nextStep,Option.bind_some]
      exact ran

theorem initial_finished (program : Program) (input : List Bool) (fuel steps : Nat) (output : Config program)
    (finished : finishWithin program fuel 0 (empty program) (initial program input)=some (steps,output)) :
    HaltsAt program input steps output := by
  obtain ⟨count,countEq,ran,halted⟩ := finishWithin_sound program fuel 0 (empty program)
    (initial program input) steps output (empty_valid program) finished
  simp only [Nat.zero_add] at countEq
  exact countEq.symm ▸ ⟨ran,halted⟩

end Counting.Machine.TestMemo
