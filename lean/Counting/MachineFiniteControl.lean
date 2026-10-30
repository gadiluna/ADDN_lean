import Counting.MachineModel

/-! Renaming an explicitly enumerable finite control into the fixed `Fin`
control used by the physical machine. Tape operations and step counts are
unchanged. The equivalence is data, so this construction is executable. -/
namespace Counting.Machine.FiniteControl

structure Config (State : Type) where
  control : State
  tape : Tape

def step {State : Type} (code : State → Symbol → Option (State × Turing.TM0.Stmt Symbol))
    (config : Config State) : Option (Config State) :=
  (code config.control config.tape.head).map (fun (control, action) =>
    ⟨control, match action with
      | .move direction => config.tape.move direction
      | .write symbol => config.tape.write symbol⟩)

def compile {State : Type} {states : Nat} (encode : State ≃ Fin (states+1))
    (code : State → Symbol → Option (State × Turing.TM0.Stmt Symbol))
    (accept : State → Bool) : Program where
  states := states
  code control symbol := (code (encode.symm control) symbol).map (fun (next, action) => (encode next,action))
  accept control := accept (encode.symm control)

def config {State : Type} {states : Nat} (encode : State ≃ Fin (states+1))
    (code : State → Symbol → Option (State × Turing.TM0.Stmt Symbol))
    (accept : State → Bool) (source : Config State) : Machine.Config (compile encode code accept) :=
  ⟨encode source.control, source.tape⟩

theorem step_compile {State : Type} {states : Nat} (encode : State ≃ Fin (states+1))
    (code : State → Symbol → Option (State × Turing.TM0.Stmt Symbol))
    (accept : State → Bool) (source : Config State) :
    Machine.step (compile encode code accept) (config encode code accept source) =
      (step code source).map (config encode code accept) := by
  simp only [Machine.step, compile, config, Equiv.symm_apply_apply, step, Option.map_map]
  rfl

theorem run_compile {State : Type} {states : Nat} (encode : State ≃ Fin (states+1))
    (code : State → Symbol → Option (State × Turing.TM0.Stmt Symbol))
    (accept : State → Bool) (steps : Nat) (source : Config State) :
    run (Machine.step (compile encode code accept)) steps (config encode code accept source) =
      (run (step code) steps source).map (config encode code accept) :=
  (run_simulation _ _ _ (fun source => (step_compile encode code accept source).symm) steps source).symm

/-- A subroutine may continue into a caller when it halts. Every successful
subroutine transition still embeds literally into the caller. -/
theorem embed_step {State : Type} (code : State → Symbol → Option (State × Turing.TM0.Stmt Symbol))
    (program : Program) (label : Control program → State)
    (instructions : ∀ control symbol next action, program.code control symbol = some (next,action) →
      code (label control) symbol = some (label next,action))
    {first last : Machine.Config program} (success : Machine.step program first = some last) :
    step code ⟨label first.control, first.tape⟩ = some ⟨label last.control,last.tape⟩ := by
  obtain ⟨⟨next,action⟩,instruction,equal⟩ := Option.map_eq_some_iff.mp success
  subst last
  simp only [step, instructions _ _ _ _ instruction, Option.map_some]
  rfl

theorem embed_run {State : Type} (code : State → Symbol → Option (State × Turing.TM0.Stmt Symbol))
    (program : Program) (label : Control program → State)
    (instructions : ∀ control symbol next action, program.code control symbol = some (next,action) →
      code (label control) symbol = some (label next,action))
    (steps : Nat) {first last : Machine.Config program}
    (success : run (Machine.step program) steps first = some last) :
    run (step code) steps ⟨label first.control,first.tape⟩ = some ⟨label last.control,last.tape⟩ := by
  induction steps generalizing first with
  | zero => have equal := Option.some.inj success; subst last; rfl
  | succ steps ih =>
      cases transition : Machine.step program first with
      | none => simp only [run, transition, Option.bind_none] at success; contradiction
      | some middle =>
          have tail : run (Machine.step program) steps middle = some last := by
            simpa only [run, transition, Option.bind_some] using success
          rw [run, embed_step code program label instructions transition, Option.bind_some]
          exact ih tail

end Counting.Machine.FiniteControl
