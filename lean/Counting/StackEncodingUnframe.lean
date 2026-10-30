import Counting.StackEncodingFrame
import Counting.MachineFrameBoot

namespace Counting.StackMachine.EncodingPrograms
open ListPrograms

/-- Parse one frame into a reversed temporary and then run the already
verified reverse routine. Control 7 means success; control 8 means truncation. -/
def unframeProgram (extra : Nat) (source target temporary : Fin (extra+3)) : Program where
  extraRegisters := extra+1
  states := 8
  code state := match state.val with
    | 0 => .pop source 8 4 1
    | 1 => .pop source 8 2 3
    | 2 => .push temporary false 0
    | 3 => .push temporary true 0
    | 4 => .pop temporary 7 5 6
    | 5 => .push target false 4
    | 6 => .push target true 4
    | _ => .halt

def unframeConfig (extra : Nat) (source target temporary : Fin (extra+3))
    (control : Control (unframeProgram extra source target temporary))
    (base : Fin (extra+3) → List Bool) (input output work : List Bool) :
    Config (unframeProgram extra source target temporary) :=
  ⟨control, fun r => if r=source then input else if r=target then output
    else if r=temporary then work else base r⟩

def restoreControl (extra : Nat) (source target temporary : Fin (extra+3))
    (control : Control (reverseProgram (extra+1) temporary target)) :
    Control (unframeProgram extra source target temporary) := ⟨control.val+4, by have := control.isLt; change control.val < 4 at this; change control.val+4 < 9; omega⟩

def restoreEmbed (extra : Nat) (source target temporary : Fin (extra+3))
    (config : Config (reverseProgram (extra+1) temporary target)) :
    Config (unframeProgram extra source target temporary) :=
  ⟨restoreControl extra source target temporary config.control, config.store⟩

theorem restore_code (extra : Nat) (source target temporary : Fin (extra+3))
    (control : Control (reverseProgram (extra+1) temporary target)) :
    (unframeProgram extra source target temporary).code (restoreControl extra source target temporary control) =
      ((reverseProgram (extra+1) temporary target).code control).relabel
        (restoreControl extra source target temporary) := by
  fin_cases control <;> rfl

theorem restore_step (extra : Nat) (source target temporary : Fin (extra+3))
    (config : Config (reverseProgram (extra+1) temporary target)) :
    step (unframeProgram extra source target temporary) (restoreEmbed extra source target temporary config) =
      (step (reverseProgram (extra+1) temporary target) config).map (restoreEmbed extra source target temporary) := by
  unfold step
  dsimp only [restoreEmbed]
  rw [restore_code]
  cases instruction : (reverseProgram (extra+1) temporary target).code config.control <;>
    simp only [Instruction.relabel, restoreEmbed, Option.map_none, Option.map_some] <;> try rfl
  split <;> simp only [Option.map_some, restoreEmbed]
  split <;> rfl

theorem restore_run (extra : Nat) (source target temporary : Fin (extra+3))
    (time : Nat) (config : Config (reverseProgram (extra+1) temporary target)) :
    Machine.run (step (unframeProgram extra source target temporary)) time
      (restoreEmbed extra source target temporary config) =
      (Machine.run (step (reverseProgram (extra+1) temporary target)) time config).map
        (restoreEmbed extra source target temporary) :=
  (Machine.run_simulation _ _ _ (fun config => (restore_step extra source target temporary config).symm) time config).symm

theorem unframe_bit (extra : Nat) (source target temporary : Fin (extra+3))
    (sw : source ≠ temporary) (tw : target ≠ temporary)
    (base : Fin (extra+3) → List Bool) (bit : Bool) (input output work : List Bool) :
    Machine.run (step (unframeProgram extra source target temporary)) 3
      (unframeConfig extra source target temporary 0 base (true::bit::input) output work) =
      some (unframeConfig extra source target temporary 0 base input output (bit::work)) := by
  cases bit <;> dsimp [Machine.run, step, unframeProgram, unframeConfig]
  all_goals
    simp [Ne.symm sw, Ne.symm tw]
    refine ⟨rfl, ?_⟩
    funext r
    by_cases first : r=source
    · subst r; simp [sw]
    · by_cases second : r=target
      · subst r; simp [tw, first]
      · by_cases third : r=temporary
        · subst r; simp [Ne.symm sw, Ne.symm tw]
        · simp [first, second, third]

theorem unframe_end (extra : Nat) (source target temporary : Fin (extra+3))
    (base : Fin (extra+3) → List Bool) (input output work : List Bool) :
    step (unframeProgram extra source target temporary)
      (unframeConfig extra source target temporary 0 base (false::input) output work) =
      some (unframeConfig extra source target temporary 4 base input output work) := by
  dsimp [step, unframeProgram, unframeConfig]
  simp
  refine ⟨rfl, ?_⟩
  funext r
  by_cases same : r=source
  · subst r; simp
  · simp [same]

theorem unframe_prefix (extra : Nat) (source target temporary : Fin (extra+3))
    (sw : source ≠ temporary) (tw : target ≠ temporary)
    (base : Fin (extra+3) → List Bool) (payload suffix output work : List Bool) :
    Machine.run (step (unframeProgram extra source target temporary)) (3*payload.length+1)
      (unframeConfig extra source target temporary 0 base (Encoding.frame payload++suffix) output work) =
      some (unframeConfig extra source target temporary 4 base suffix output (payload.reverse++work)) := by
  induction payload generalizing work with
  | nil =>
    rw [show 3*([].length)+1=1 by rfl, Machine.run]
    change (step (unframeProgram extra source target temporary)
      (unframeConfig extra source target temporary 0 base (false::suffix) output work)).bind _ = _
    rw [unframe_end, Option.bind_some]
    rfl
  | cons bit payload ih =>
    rw [List.length_cons, show 3*(payload.length+1)+1=3+(3*payload.length+1) by omega,
      Machine.run_add]
    simp only [Encoding.frame, List.cons_append]
    rw [unframe_bit extra source target temporary sw tw, Option.bind_some, ih]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

theorem unframe_restore (extra : Nat) (source target temporary : Fin (extra+3))
    (st : source ≠ target) (sw : source ≠ temporary) (tw : target ≠ temporary)
    (base : Fin (extra+3) → List Bool) (input output work : List Bool) :
    Machine.run (step (unframeProgram extra source target temporary)) (2*work.length+1)
      (unframeConfig extra source target temporary 4 base input output work) =
      some (unframeConfig extra source target temporary 7 base input (work.reverse++output) []) := by
  let store := (unframeConfig extra source target temporary 4 base input output work).store
  have start : unframeConfig extra source target temporary 4 base input output work =
      restoreEmbed extra source target temporary
        (reverseConfig (extra+1) temporary target 0 store work output) := by
    apply congrArg (Config.mk _)
    change (fun r : Fin (extra+3) => if r=source then input else if r=target then output else
      if r=temporary then work else base r) = (fun r : Fin (extra+3) => if r=temporary then work else
      if r=target then output else if r=source then input else if r=target then output else if r=temporary then work else base r)
    funext r
    by_cases a : r=source
    · subst r; simp [st, sw]
    · by_cases b : r=target
      · subst r; simp [Ne.symm st, tw]
      · by_cases c : r=temporary
        · subst r; simp [Ne.symm sw, Ne.symm tw]
        · simp [a, b, c]
  rw [start, restore_run, reverse_run (extra+1) temporary target (Ne.symm tw), Option.map_some]
  apply congrArg some
  apply congrArg (Config.mk _)
  change (fun r : Fin (extra+3) => if r=temporary then [] else if r=target then work.reverse++output
    else if r=source then input else if r=target then output else if r=temporary then work else base r) =
    (fun r : Fin (extra+3) => if r=source then input else if r=target then work.reverse++output else
      if r=temporary then [] else base r)
  funext r
  by_cases a : r=source
  · subst r; simp [st, sw]
  · by_cases b : r=target
    · subst r; simp [Ne.symm st, tw]
    · by_cases c : r=temporary
      · subst r; simp [Ne.symm sw, Ne.symm tw]
      · simp [a, b, c]

/-- Exact parser effect and count, including retained suffix and untouched
registers. No population identity or uncharged decoder occurs in the code. -/
theorem unframe_frames (extra : Nat) (source target temporary : Fin (extra+3))
    (st : source ≠ target) (sw : source ≠ temporary) (tw : target ≠ temporary)
    (base : Fin (extra+3) → List Bool) (payload suffix output : List Bool) :
    Machine.run (step (unframeProgram extra source target temporary)) (5*payload.length+2)
      (unframeConfig extra source target temporary 0 base (Encoding.frame payload++suffix) output []) =
      some (unframeConfig extra source target temporary 7 base suffix (payload++output) []) := by
  rw [show 5*payload.length+2=(3*payload.length+1)+(2*payload.length+1) by omega,
    Machine.run_add, unframe_prefix extra source target temporary sw tw, Option.bind_some, List.append_nil]
  simpa only [List.length_reverse, List.reverse_reverse] using
    unframe_restore extra source target temporary st sw tw base suffix output payload.reverse

theorem unframe_halted (extra : Nat) (source target temporary : Fin (extra+3))
    (base : Fin (extra+3) → List Bool) (input output work : List Bool) :
    step (unframeProgram extra source target temporary)
      (unframeConfig extra source target temporary 7 base input output work) = none ∧
    step (unframeProgram extra source target temporary)
      (unframeConfig extra source target temporary 8 base input output work) = none := ⟨rfl,rfl⟩

end Counting.StackMachine.EncodingPrograms
