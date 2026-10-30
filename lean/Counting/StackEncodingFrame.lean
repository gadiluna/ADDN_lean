import Counting.StackListPrograms
import Counting.StackRoutineSemantics
import Counting.StackArithmeticOutput
import Counting.StackCompilerComplete

/-! A concrete framing transducer. All reversal and output operations are
stack instructions, with a proved instruction count and physical compiler
bound; the executable code never calls a Lean list encoder. -/
namespace Counting.StackMachine.EncodingPrograms
open ListPrograms Arithmetic

def frameReverseProgram (extra : Nat) (source target : Fin (extra+2)) : Program where
  extraRegisters := extra
  states := 5
  code state := match state.val with
    | 0 => .push target false 1
    | 1 => .pop source 5 2 3
    | 2 => .push target false 4
    | 3 => .push target true 4
    | 4 => .push target true 1
    | _ => .halt

def frameReverseConfig (extra : Nat) (source target : Fin (extra+2))
    (control : Control (frameReverseProgram extra source target))
    (base : Fin (extra+2) → List Bool) (input output : List Bool) :
    Config (frameReverseProgram extra source target) :=
  ⟨control, fun r => if r=source then input else if r=target then output else base r⟩

theorem frameReverse_bit (extra : Nat) (source target : Fin (extra+2)) (distinct : source ≠ target)
    (base : Fin (extra+2) → List Bool) (bit : Bool) (input output : List Bool) :
    Machine.run (step (frameReverseProgram extra source target)) 3
      (frameReverseConfig extra source target 1 base (bit::input) output) =
      some (frameReverseConfig extra source target 1 base input (true::bit::output)) := by
  cases bit <;> dsimp [Machine.run, step, frameReverseProgram, frameReverseConfig]
  all_goals
    simp [Ne.symm distinct]
    refine ⟨rfl, ?_⟩
    funext r
    by_cases first : r=source
    · subst r; simp [distinct]
    · by_cases second : r=target
      · subst r; simp [Ne.symm distinct]
      · simp [first, second]

theorem frameReverse_empty (extra : Nat) (source target : Fin (extra+2))
    (base : Fin (extra+2) → List Bool) (output : List Bool) :
    step (frameReverseProgram extra source target)
      (frameReverseConfig extra source target 1 base [] output) =
      some (frameReverseConfig extra source target 5 base [] output) := by
  simp [step, frameReverseProgram, frameReverseConfig]
  rfl

theorem frameReverse_loop (extra : Nat) (source target : Fin (extra+2)) (distinct : source ≠ target)
    (base : Fin (extra+2) → List Bool) (input output : List Bool) :
    Machine.run (step (frameReverseProgram extra source target)) (3*input.length+1)
      (frameReverseConfig extra source target 1 base input output) =
      some (frameReverseConfig extra source target 5 base [] (frameBody input.reverse++output)) := by
  induction input generalizing output with
  | nil =>
    rw [show 3*([].length)+1=1 by rfl, Machine.run, frameReverse_empty, Option.bind_some]
    rfl
  | cons bit input ih =>
    rw [List.length_cons, show 3*(input.length+1)+1=3+(3*input.length+1) by omega,
      Machine.run_add, frameReverse_bit extra source target distinct, Option.bind_some, ih,
      List.reverse_cons, frameBody_append]
    simp only [frameBody, List.flatMap_cons, List.flatMap_nil, List.append_assoc,
      List.cons_append, List.nil_append]

theorem frameReverse_start (extra : Nat) (source target : Fin (extra+2)) (distinct : source ≠ target)
    (base : Fin (extra+2) → List Bool) (input output : List Bool) :
    step (frameReverseProgram extra source target)
      (frameReverseConfig extra source target 0 base input output) =
      some (frameReverseConfig extra source target 1 base input (false::output)) := by
  simp only [step, frameReverseProgram, frameReverseConfig]
  simp [Ne.symm distinct]
  refine ⟨rfl, ?_⟩
  funext r
  by_cases first : r=source
  · subst r; simp [distinct]
  · by_cases second : r=target
    · subst r; simp [Ne.symm distinct]
    · simp [first, second]

theorem frameReverse_run (extra : Nat) (source target : Fin (extra+2)) (distinct : source ≠ target)
    (base : Fin (extra+2) → List Bool) (input output : List Bool) :
    Machine.run (step (frameReverseProgram extra source target)) (3*input.length+2)
      (frameReverseConfig extra source target 0 base input output) =
      some (frameReverseConfig extra source target 5 base [] (Encoding.frame input.reverse++output)) := by
  rw [show 3*input.length+2=(3*input.length+1)+1 by omega, Machine.run,
    frameReverse_start extra source target distinct, Option.bind_some, frameReverse_loop extra source target distinct]
  rw [frame_eq_body, List.append_assoc]
  rfl

theorem frameReverse_halted (extra : Nat) (source target : Fin (extra+2))
    (base : Fin (extra+2) → List Bool) (input output : List Bool) :
    step (frameReverseProgram extra source target)
      (frameReverseConfig extra source target 5 base input output) = none := rfl

def frameRoutine (extra : Nat) (source target temporary : Fin (extra+3)) : Routine (extra+1) :=
  Routine.sequence (Routine.ofProgram (reverseProgram (extra+1) source temporary))
    (Routine.ofProgram (frameReverseProgram (extra+1) temporary target))

def frameResult (extra : Nat) (source target temporary : Fin (extra+3))
    (store : Fin (extra+3) → List Bool) : Fin (extra+3) → List Bool :=
  fun r => if r=source then [] else if r=target then Encoding.frame (store source)++store target
    else if r=temporary then [] else store r

/-- Generic framing routine: consumes its source, prepends the framed
payload to its target, clears its temporary, and preserves other registers. -/
theorem frame_executes (extra : Nat) (source target temporary : Fin (extra+3))
    (st : source ≠ target) (sw : source ≠ temporary) (tw : target ≠ temporary)
    (store : Fin (extra+3) → List Bool) (empty : store temporary = []) :
    Routine.Executes (frameRoutine extra source target temporary) store (5*(store source).length+4)
      (frameResult extra source target temporary store) := by
  let middle := reverseConfig (extra+1) source temporary 3 store [] (store source).reverse
  have start : (⟨0,store⟩ : Config (reverseProgram (extra+1) source temporary)) =
      reverseConfig (extra+1) source temporary 0 store (store source) [] := by
    apply congrArg (Config.mk _)
    change store = (fun r : Fin (extra+3) => if r=source then store source else if r=temporary then [] else store r)
    funext r
    by_cases first : r=source
    · subst r; simp
    · by_cases second : r=temporary
      · subst r; simp [first, empty]
      · simp [first, second]
  have firstRun : Routine.Executes (Routine.ofProgram (reverseProgram (extra+1) source temporary))
      store (2*(store source).length+1) middle.store := by
    refine ⟨middle, ?_, reverse_halted _ _ _ _ _ _, rfl⟩
    change Machine.run (step (reverseProgram (extra+1) source temporary)) _ ⟨0,store⟩ = some middle
    rw [start]
    simpa only [List.append_nil] using reverse_run (extra+1) source temporary sw store (store source) []
  have secondStart : (⟨0,middle.store⟩ : Config (frameReverseProgram (extra+1) temporary target)) =
      frameReverseConfig (extra+1) temporary target 0 middle.store (store source).reverse (store target) := by
    apply congrArg (Config.mk _)
    change (fun r : Fin (extra+3) => if r=source then [] else if r=temporary then (store source).reverse else store r) =
      (fun r : Fin (extra+3) => if r=temporary then (store source).reverse else if r=target then store target else
        if r=source then [] else if r=temporary then (store source).reverse else store r)
    funext r
    by_cases first : r=temporary
    · subst r; simp [Ne.symm sw]
    · by_cases second : r=target
      · subst r; simp [Ne.symm st, tw]
      · simp [first, second]
  let finish := frameReverseConfig (extra+1) temporary target 5 middle.store []
    (Encoding.frame (store source)++store target)
  have finalStore : finish.store = frameResult extra source target temporary store := by
    change (fun r : Fin (extra+3) => if r=temporary then [] else if r=target then
      Encoding.frame (store source)++store target else if r=source then [] else if r=temporary then
      (store source).reverse else store r) = (fun r : Fin (extra+3) => if r=source then [] else
      if r=target then Encoding.frame (store source)++store target else if r=temporary then [] else store r)
    funext r
    by_cases first : r=source
    · subst r; simp [st, sw]
    · by_cases second : r=target
      · subst r; simp [Ne.symm st, tw]
      · by_cases third : r=temporary
        · subst r; simp [Ne.symm sw, Ne.symm tw]
        · simp [first, second, third]
  have secondRun : Routine.Executes (Routine.ofProgram (frameReverseProgram (extra+1) temporary target))
      middle.store (3*(store source).length+2) (frameResult extra source target temporary store) := by
    refine ⟨finish, ?_, frameReverse_halted _ _ _ _ _ _, finalStore⟩
    change Machine.run (step (frameReverseProgram (extra+1) temporary target)) _ ⟨0,middle.store⟩ = some finish
    rw [secondStart]
    simpa only [List.length_reverse, List.reverse_reverse] using
      frameReverse_run (extra+1) temporary target (Ne.symm tw) middle.store (store source).reverse (store target)
  have combined := firstRun.sequence secondRun
  have time : (2*(store source).length+1)+1+(3*(store source).length+2)=5*(store source).length+4 := by omega
  rw [time] at combined
  exact combined

def frameProgram : Program := (frameRoutine 0 0 1 2).program

theorem frame_computes : ComputesIn frameProgram Encoding.frame (fun length => 5*length+4) := by
  intro input
  let store : Fin 3 → List Bool := fun r => if r=0 then input else []
  obtain ⟨finish, ran, halted, result⟩ := frame_executes 0 0 1 2 (by decide) (by decide) (by decide)
    store (by rfl)
  refine ⟨5*input.length+4, finish, le_rfl, ⟨ran, halted⟩, ?_⟩
  rw [result]
  simp [frameResult, store]

theorem frame_computesCleanIn : Complexity.ComputesCleanIn (Compiler.compile frameProgram) Encoding.frame
    (Complexity.polynomial (20*(5+1+5)^2) 4) := by
  apply Compiler.computesCleanIn_polynomial 5 1
  intro input
  obtain ⟨time, output, bound, halted, value⟩ := frame_computes input
  refine ⟨time, output, ?_, halted, value⟩
  simp only [Complexity.polynomial, pow_one]
  dsimp only at bound
  omega

end Counting.StackMachine.EncodingPrograms
