import Counting.StackListPrograms

namespace Counting.StackMachine.Unary

/-- Measure a stack while restoring the source. A third register is temporary;
its required initial emptiness is explicit in `length_run`. -/
def lengthProgram (extra : Nat) (source target temporary : Fin (extra+3)) : Program where
  extraRegisters := extra+1
  states := 8
  code state := match state.val with
    | 0 => .pop source 3 1 2
    | 1 => .push temporary false 0
    | 2 => .push temporary true 0
    | 3 => .pop temporary 8 4 5
    | 4 => .push source false 6
    | 5 => .push source true 7
    | 6 => .push target true 3
    | 7 => .push target true 3
    | _ => .halt

def lengthConfig (extra : Nat) (source target temporary : Fin (extra+3))
    (state : Control (lengthProgram extra source target temporary))
    (base : Fin (extra+3) → List Bool) (input output work : List Bool) :
    Config (lengthProgram extra source target temporary) :=
  ⟨state, fun r => if r=source then input else if r=target then output else if r=temporary then work else base r⟩

theorem length_prepare_bit (extra : Nat) (source target temporary : Fin (extra+3))
    (st : source ≠ target) (sw : source ≠ temporary) (tw : target ≠ temporary)
    (base : Fin (extra+3) → List Bool) (bit : Bool) (input output work : List Bool) :
    Machine.run (step (lengthProgram extra source target temporary)) 2
      (lengthConfig extra source target temporary 0 base (bit::input) output work) =
      some (lengthConfig extra source target temporary 0 base input output (bit::work)) := by
  cases bit <;> simp only [Machine.run, step, lengthProgram, lengthConfig]
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

theorem length_prepare_empty (extra : Nat) (source target temporary : Fin (extra+3))
    (base : Fin (extra+3) → List Bool) (output work : List Bool) :
    step (lengthProgram extra source target temporary)
      (lengthConfig extra source target temporary 0 base [] output work) =
      some (lengthConfig extra source target temporary 3 base [] output work) := by
  simp [step, lengthProgram, lengthConfig]
  rfl

theorem length_prepare_run (extra : Nat) (source target temporary : Fin (extra+3))
    (st : source ≠ target) (sw : source ≠ temporary) (tw : target ≠ temporary)
    (base : Fin (extra+3) → List Bool) (input output work : List Bool) :
    Machine.run (step (lengthProgram extra source target temporary)) (2*input.length+1)
      (lengthConfig extra source target temporary 0 base input output work) =
      some (lengthConfig extra source target temporary 3 base [] output (input.reverse++work)) := by
  induction input generalizing work with
  | nil =>
      rw [show 2*([].length)+1=1 by rfl, Machine.run, length_prepare_empty, Option.bind_some]
      rfl
  | cons bit input ih =>
      rw [List.length_cons, show 2*(input.length+1)+1=2+(2*input.length+1) by omega,
        Machine.run_add, length_prepare_bit extra source target temporary st sw tw, Option.bind_some, ih]
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

theorem length_restore_bit (extra : Nat) (source target temporary : Fin (extra+3))
    (st : source ≠ target) (sw : source ≠ temporary) (tw : target ≠ temporary)
    (base : Fin (extra+3) → List Bool) (bit : Bool) (input output work : List Bool) :
    Machine.run (step (lengthProgram extra source target temporary)) 3
      (lengthConfig extra source target temporary 3 base input output (bit::work)) =
      some (lengthConfig extra source target temporary 3 base (bit::input) (true::output) work) := by
  cases bit <;> dsimp [Machine.run, step, lengthProgram, lengthConfig]
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

theorem length_restore_empty (extra : Nat) (source target temporary : Fin (extra+3))
    (sw : source ≠ temporary) (tw : target ≠ temporary)
    (base : Fin (extra+3) → List Bool) (input output : List Bool) :
    step (lengthProgram extra source target temporary)
      (lengthConfig extra source target temporary 3 base input output []) =
      some (lengthConfig extra source target temporary 8 base input output []) := by
  simp [step, lengthProgram, lengthConfig, Ne.symm sw, Ne.symm tw]
  rfl

theorem length_restore_run (extra : Nat) (source target temporary : Fin (extra+3))
    (st : source ≠ target) (sw : source ≠ temporary) (tw : target ≠ temporary)
    (base : Fin (extra+3) → List Bool) (input output work : List Bool) :
    Machine.run (step (lengthProgram extra source target temporary)) (3*work.length+1)
      (lengthConfig extra source target temporary 3 base input output work) =
      some (lengthConfig extra source target temporary 8 base (work.reverse++input) (List.replicate work.length true++output) []) := by
  induction work generalizing input output with
  | nil =>
      rw [show 3*([].length)+1=1 by rfl, Machine.run, length_restore_empty _ _ _ _ sw tw, Option.bind_some]
      rfl
  | cons bit work ih =>
      rw [List.length_cons, show 3*(work.length+1)+1=3+(3*work.length+1) by omega,
        Machine.run_add, length_restore_bit extra source target temporary st sw tw, Option.bind_some, ih]
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append, List.replicate_succ']

/-- The source is restored exactly, one true bit is emitted per source bit, and
all registers outside the stated three are preserved. -/
theorem length_run (extra : Nat) (source target temporary : Fin (extra+3))
    (st : source ≠ target) (sw : source ≠ temporary) (tw : target ≠ temporary)
    (base : Fin (extra+3) → List Bool) (input output : List Bool) :
    Machine.run (step (lengthProgram extra source target temporary)) (5*input.length+2)
      (lengthConfig extra source target temporary 0 base input output []) =
      some (lengthConfig extra source target temporary 8 base input (List.replicate input.length true++output) []) := by
  rw [show 5*input.length+2=(2*input.length+1)+(3*input.length+1) by omega,
    Machine.run_add, length_prepare_run extra source target temporary st sw tw,
    Option.bind_some, List.append_nil, ← List.length_reverse (as := input),
    length_restore_run extra source target temporary st sw tw,
    List.reverse_reverse, List.append_nil, List.length_reverse]

theorem length_halted (extra : Nat) (source target temporary : Fin (extra+3))
    (base : Fin (extra+3) → List Bool) (input output work : List Bool) :
    step (lengthProgram extra source target temporary)
      (lengthConfig extra source target temporary 8 base input output work) = none := rfl

theorem length_computes : ComputesIn (lengthProgram 0 0 1 2)
    (fun input => List.replicate input.length true) (fun length => 5*length+2) := by
  intro input
  let base : Fin 3 → List Bool := fun _ => []
  refine ⟨5*input.length+2,
    lengthConfig 0 0 1 2 8 base input (List.replicate input.length true) [], le_rfl,
    ⟨?_, length_halted _ _ _ _ _ _ _ _⟩, rfl⟩
  have start : initial (lengthProgram 0 0 1 2) input = lengthConfig 0 0 1 2 0 base input [] [] := by
    apply congrArg (Config.mk _)
    funext r
    fin_cases r <;> rfl
  rw [start]
  simpa only [List.append_nil] using
    length_run 0 0 1 2 (by decide) (by decide) (by decide) base input []

end Counting.StackMachine.Unary
