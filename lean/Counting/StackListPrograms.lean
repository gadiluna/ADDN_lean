import Counting.StackMachine

namespace Counting.StackMachine.ListPrograms

/-- Destructively reverse one register onto another. The two instructions
per bit are explicit `pop`/`push` operations of the compiled stack language. -/
def reverseProgram (extra : Nat) (source target : Fin (extra+2)) : Program where
  extraRegisters := extra
  states := 3
  code state := match state.val with
    | 0 => .pop source 3 1 2
    | 1 => .push target false 0
    | 2 => .push target true 0
    | _ => .halt

def reverseConfig (extra : Nat) (source target : Fin (extra+2))
    (state : Control (reverseProgram extra source target))
    (base : Fin (extra+2) → List Bool) (input output : List Bool) :
    Config (reverseProgram extra source target) :=
  ⟨state, fun r => if r=source then input else if r=target then output else base r⟩

theorem reverse_bit (extra : Nat) (source target : Fin (extra+2)) (distinct : source ≠ target)
    (base : Fin (extra+2) → List Bool) (bit : Bool) (input output : List Bool) :
    Machine.run (step (reverseProgram extra source target)) 2
      (reverseConfig extra source target 0 base (bit::input) output) =
      some (reverseConfig extra source target 0 base input (bit::output)) := by
  cases bit <;>
    simp only [Machine.run, step, reverseProgram, reverseConfig]
  all_goals
    simp [Ne.symm distinct]
    refine ⟨rfl, ?_⟩
    funext r
    by_cases a : r=source
    · subst r; simp [distinct]
    · by_cases b : r=target
      · subst r; simp [Ne.symm distinct]
      · simp [a, b]

theorem reverse_empty (extra : Nat) (source target : Fin (extra+2))
    (base : Fin (extra+2) → List Bool) (output : List Bool) :
    step (reverseProgram extra source target) (reverseConfig extra source target 0 base [] output) =
      some (reverseConfig extra source target 3 base [] output) := by
  simp [step, reverseProgram, reverseConfig]
  rfl

/-- Exact instruction count and preservation of every other register. -/
theorem reverse_run (extra : Nat) (source target : Fin (extra+2)) (distinct : source ≠ target)
    (base : Fin (extra+2) → List Bool) (input output : List Bool) :
    Machine.run (step (reverseProgram extra source target)) (2*input.length+1)
      (reverseConfig extra source target 0 base input output) =
      some (reverseConfig extra source target 3 base [] (input.reverse++output)) := by
  induction input generalizing output with
  | nil =>
      rw [show 2*([].length)+1=1 by rfl, Machine.run, reverse_empty, Option.bind_some]
      rfl
  | cons bit input ih =>
      rw [List.length_cons, show 2*(input.length+1)+1=2+(2*input.length+1) by omega,
        Machine.run_add, reverse_bit extra source target distinct, Option.bind_some, ih]
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

theorem reverse_halted (extra : Nat) (source target : Fin (extra+2))
    (base : Fin (extra+2) → List Bool) (input output : List Bool) :
    step (reverseProgram extra source target) (reverseConfig extra source target 3 base input output) = none := rfl

/-- A complete input-to-output reverse program, with no unaccounted list
operation in its executed code. -/
theorem reverse_computes : ComputesIn (reverseProgram 0 0 1) List.reverse (fun length => 2*length+1) := by
  intro input
  let base : Fin 2 → List Bool := fun _ => []
  refine ⟨2*input.length+1, reverseConfig 0 0 1 3 base [] input.reverse, le_rfl, ⟨?_, reverse_halted _ _ _ _ _ _⟩, rfl⟩
  have start : initial (reverseProgram 0 0 1) input = reverseConfig 0 0 1 0 base input [] := by
    apply congrArg (Config.mk _)
    funext r
    fin_cases r <;> rfl
  rw [start]
  simpa only [List.append_nil] using reverse_run 0 0 1 (by decide) base input []

/-- Copy a stack while restoring the source. A third register is temporary;
its required initial emptiness is explicit in `copy_run`. -/
def copyProgram (extra : Nat) (source target temporary : Fin (extra+3)) : Program where
  extraRegisters := extra+1
  states := 8
  code state := match state.val with
    | 0 => .pop source 3 1 2
    | 1 => .push temporary false 0
    | 2 => .push temporary true 0
    | 3 => .pop temporary 8 4 5
    | 4 => .push source false 6
    | 5 => .push source true 7
    | 6 => .push target false 3
    | 7 => .push target true 3
    | _ => .halt

def copyConfig (extra : Nat) (source target temporary : Fin (extra+3))
    (state : Control (copyProgram extra source target temporary))
    (base : Fin (extra+3) → List Bool) (input output work : List Bool) :
    Config (copyProgram extra source target temporary) :=
  ⟨state, fun r => if r=source then input else if r=target then output else if r=temporary then work else base r⟩

theorem copy_prepare_bit (extra : Nat) (source target temporary : Fin (extra+3))
    (st : source ≠ target) (sw : source ≠ temporary) (tw : target ≠ temporary)
    (base : Fin (extra+3) → List Bool) (bit : Bool) (input output work : List Bool) :
    Machine.run (step (copyProgram extra source target temporary)) 2
      (copyConfig extra source target temporary 0 base (bit::input) output work) =
      some (copyConfig extra source target temporary 0 base input output (bit::work)) := by
  cases bit <;> simp only [Machine.run, step, copyProgram, copyConfig]
  all_goals
    simp [Ne.symm sw, Ne.symm tw]
    refine ⟨rfl, ?_⟩
    funext r
    by_cases a : r=source
    · subst r; simp [sw]
    · by_cases b : r=target
      · subst r; simp [Ne.symm st, tw]
      · by_cases c : r=temporary
        · subst r; simp [Ne.symm sw, Ne.symm tw]
        · simp [a, b, c]

theorem copy_prepare_empty (extra : Nat) (source target temporary : Fin (extra+3))
    (base : Fin (extra+3) → List Bool) (output work : List Bool) :
    step (copyProgram extra source target temporary)
      (copyConfig extra source target temporary 0 base [] output work) =
      some (copyConfig extra source target temporary 3 base [] output work) := by
  simp [step, copyProgram, copyConfig]
  rfl

theorem copy_prepare_run (extra : Nat) (source target temporary : Fin (extra+3))
    (st : source ≠ target) (sw : source ≠ temporary) (tw : target ≠ temporary)
    (base : Fin (extra+3) → List Bool) (input output work : List Bool) :
    Machine.run (step (copyProgram extra source target temporary)) (2*input.length+1)
      (copyConfig extra source target temporary 0 base input output work) =
      some (copyConfig extra source target temporary 3 base [] output (input.reverse++work)) := by
  induction input generalizing work with
  | nil =>
      rw [show 2*([].length)+1=1 by rfl, Machine.run, copy_prepare_empty, Option.bind_some]
      rfl
  | cons bit input ih =>
      rw [List.length_cons, show 2*(input.length+1)+1=2+(2*input.length+1) by omega,
        Machine.run_add, copy_prepare_bit extra source target temporary st sw tw, Option.bind_some, ih]
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

theorem copy_restore_bit (extra : Nat) (source target temporary : Fin (extra+3))
    (st : source ≠ target) (sw : source ≠ temporary) (tw : target ≠ temporary)
    (base : Fin (extra+3) → List Bool) (bit : Bool) (input output work : List Bool) :
    Machine.run (step (copyProgram extra source target temporary)) 3
      (copyConfig extra source target temporary 3 base input output (bit::work)) =
      some (copyConfig extra source target temporary 3 base (bit::input) (bit::output) work) := by
  cases bit <;> dsimp [Machine.run, step, copyProgram, copyConfig]
  all_goals
    simp [Ne.symm st, Ne.symm sw, Ne.symm tw, sw, tw]
    refine ⟨rfl, ?_⟩
    funext r
    by_cases a : r=source
    · subst r; simp [st]
    · by_cases b : r=target
      · subst r; simp [Ne.symm st]
      · by_cases c : r=temporary
        · subst r; simp [Ne.symm sw, Ne.symm tw]
        · simp [a, b, c]

theorem copy_restore_empty (extra : Nat) (source target temporary : Fin (extra+3))
    (sw : source ≠ temporary) (tw : target ≠ temporary)
    (base : Fin (extra+3) → List Bool) (input output : List Bool) :
    step (copyProgram extra source target temporary)
      (copyConfig extra source target temporary 3 base input output []) =
      some (copyConfig extra source target temporary 8 base input output []) := by
  simp [step, copyProgram, copyConfig, Ne.symm sw, Ne.symm tw]
  rfl

theorem copy_restore_run (extra : Nat) (source target temporary : Fin (extra+3))
    (st : source ≠ target) (sw : source ≠ temporary) (tw : target ≠ temporary)
    (base : Fin (extra+3) → List Bool) (input output work : List Bool) :
    Machine.run (step (copyProgram extra source target temporary)) (3*work.length+1)
      (copyConfig extra source target temporary 3 base input output work) =
      some (copyConfig extra source target temporary 8 base (work.reverse++input) (work.reverse++output) []) := by
  induction work generalizing input output with
  | nil =>
      rw [show 3*([].length)+1=1 by rfl, Machine.run, copy_restore_empty _ _ _ _ sw tw, Option.bind_some]
      rfl
  | cons bit work ih =>
      rw [List.length_cons, show 3*(work.length+1)+1=3+(3*work.length+1) by omega,
        Machine.run_add, copy_restore_bit extra source target temporary st sw tw, Option.bind_some, ih]
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

/-- The source is restored exactly, the temporary register is cleared, and
all registers outside the stated three are preserved. -/
theorem copy_run (extra : Nat) (source target temporary : Fin (extra+3))
    (st : source ≠ target) (sw : source ≠ temporary) (tw : target ≠ temporary)
    (base : Fin (extra+3) → List Bool) (input output : List Bool) :
    Machine.run (step (copyProgram extra source target temporary)) (5*input.length+2)
      (copyConfig extra source target temporary 0 base input output []) =
      some (copyConfig extra source target temporary 8 base input (input++output) []) := by
  rw [show 5*input.length+2=(2*input.length+1)+(3*input.length+1) by omega,
    Machine.run_add, copy_prepare_run extra source target temporary st sw tw,
    Option.bind_some, List.append_nil, ← List.length_reverse (as := input),
    copy_restore_run extra source target temporary st sw tw,
    List.reverse_reverse, List.append_nil]

theorem copy_halted (extra : Nat) (source target temporary : Fin (extra+3))
    (base : Fin (extra+3) → List Bool) (input output work : List Bool) :
    step (copyProgram extra source target temporary)
      (copyConfig extra source target temporary 8 base input output work) = none := rfl

theorem copy_computes : ComputesIn (copyProgram 0 0 1 2) id (fun length => 5*length+2) := by
  intro input
  let base : Fin 3 → List Bool := fun _ => []
  refine ⟨5*input.length+2, copyConfig 0 0 1 2 8 base input input [], le_rfl,
    ⟨?_, copy_halted _ _ _ _ _ _ _ _⟩, rfl⟩
  have start : initial (copyProgram 0 0 1 2) input = copyConfig 0 0 1 2 0 base input [] [] := by
    apply congrArg (Config.mk _)
    funext r
    fin_cases r <;> rfl
  rw [start]
  simpa only [List.append_nil] using copy_run 0 0 1 2 (by decide) (by decide) (by decide) base input []

end Counting.StackMachine.ListPrograms
