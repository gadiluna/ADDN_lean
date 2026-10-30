import Counting.StackRoutineLists
import Counting.StackArithmeticOutput

/-! Generic normalization and framing of little-endian arithmetic payloads. -/
namespace Counting.StackMachine.Normalize
open Arithmetic

def reversedProgram (extra : Nat) (source target : Fin (extra+2)) : Program where
  extraRegisters := extra
  states := 7
  code control := match control.val with
    | 0 => .push target false 1
    | 1 => .pop source 7 1 2
    | 2 => .push target true 4
    | 3 => .push target false 4
    | 4 => .push target true 5
    | 5 => .pop source 7 3 2
    | _ => .halt

def reversedConfig (extra : Nat) (source target : Fin (extra+2))
    (control : Control (reversedProgram extra source target))
    (base : Fin (extra+2) → List Bool) (input output : List Bool) :
    Config (reversedProgram extra source target) :=
  ⟨control, fun r => if r=source then input else if r=target then output else base r⟩

theorem emit_bit (extra : Nat) (source target : Fin (extra+2)) (distinct : source ≠ target)
    (base : Fin (extra+2) → List Bool) (bit : Bool) (input output : List Bool) :
    Machine.run (step (reversedProgram extra source target)) 3
      (reversedConfig extra source target 5 base (bit::input) output) =
      some (reversedConfig extra source target 5 base input (true::bit::output)) := by
  cases bit <;> simp [Machine.run,step,reversedProgram,reversedConfig,Ne.symm distinct]
  all_goals
    refine ⟨rfl,?_⟩
    funext r
    by_cases a : r=source
    · subst r; simp [distinct]
    · by_cases b : r=target
      · subst r; simp [Ne.symm distinct]
      · simp [a,b]

theorem emit_end (extra : Nat) (source target : Fin (extra+2))
    (base : Fin (extra+2) → List Bool) (output : List Bool) :
    step (reversedProgram extra source target) (reversedConfig extra source target 5 base [] output) =
      some (reversedConfig extra source target 7 base [] output) := by
  simp [step,reversedProgram,reversedConfig]
  rfl

theorem emit_run (extra : Nat) (source target : Fin (extra+2)) (distinct : source ≠ target)
    (base : Fin (extra+2) → List Bool) (input output : List Bool) :
    Machine.run (step (reversedProgram extra source target)) (3*input.length+1)
      (reversedConfig extra source target 5 base input output) =
      some (reversedConfig extra source target 7 base [] (frameBody input.reverse++output)) := by
  induction input generalizing output with
  | nil => rw [show 3*([].length)+1=1 by rfl,Machine.run,emit_end,Option.bind_some]; rfl
  | cons bit input ih =>
      rw [List.length_cons,show 3*(input.length+1)+1=3+(3*input.length+1) by omega,
        Machine.run_add,emit_bit extra source target distinct,Option.bind_some,ih,
        List.reverse_cons,frameBody_append]
      simp only [frameBody,List.flatMap_cons,List.flatMap_nil,List.append_assoc,
        List.cons_append,List.nil_append]

theorem strip_zero (extra : Nat) (source target : Fin (extra+2))
    (base : Fin (extra+2) → List Bool) (input output : List Bool) :
    step (reversedProgram extra source target) (reversedConfig extra source target 1 base (false::input) output) =
      some (reversedConfig extra source target 1 base input output) := by
  simp [step,reversedProgram,reversedConfig]
  refine ⟨rfl,?_⟩
  funext r
  by_cases same : r=source <;> simp [same]

theorem strip_one (extra : Nat) (source target : Fin (extra+2)) (distinct : source ≠ target)
    (base : Fin (extra+2) → List Bool) (input output : List Bool) :
    Machine.run (step (reversedProgram extra source target)) 3
      (reversedConfig extra source target 1 base (true::input) output) =
      some (reversedConfig extra source target 5 base input (true::true::output)) := by
  simp [Machine.run,step,reversedProgram,reversedConfig,Ne.symm distinct]
  refine ⟨rfl,?_⟩
  funext r
  by_cases a : r=source
  · subst r; simp [distinct]
  · by_cases b : r=target
    · subst r; simp [Ne.symm distinct]
    · simp [a,b]

theorem strip_end (extra : Nat) (source target : Fin (extra+2))
    (base : Fin (extra+2) → List Bool) (output : List Bool) :
    step (reversedProgram extra source target) (reversedConfig extra source target 1 base [] output) =
      some (reversedConfig extra source target 7 base [] output) := by
  simp [step,reversedProgram,reversedConfig]
  rfl

def stripCost : List Bool → Nat
  | [] => 1
  | false::bits => stripCost bits+1
  | true::bits => 3+(3*bits.length+1)

theorem stripCost_le (bits : List Bool) : stripCost bits ≤ 3*bits.length+1 := by
  induction bits with
  | nil => rfl
  | cons bit bits ih => cases bit <;> simp only [stripCost,List.length_cons] <;> omega

/-- Strip only redundant most-significant zeroes; the preexisting output
suffix is preserved rather than silently required to be empty. -/
theorem strip_run (extra : Nat) (source target : Fin (extra+2)) (distinct : source ≠ target)
    (base : Fin (extra+2) → List Bool) (input suffix : List Bool) :
    Machine.run (step (reversedProgram extra source target)) (stripCost input)
      (reversedConfig extra source target 1 base input (false::suffix)) =
      some (reversedConfig extra source target 7 base [] (Encoding.frame (normalize input.reverse)++suffix)) := by
  induction input with
  | nil => rw [stripCost,Machine.run,strip_end,Option.bind_some]; rfl
  | cons bit input ih =>
      cases bit with
      | false =>
          rw [stripCost,Machine.run,strip_zero,Option.bind_some,ih,List.reverse_cons,normalize_append_false]
      | true =>
          rw [stripCost,Machine.run_add,strip_one extra source target distinct,Option.bind_some,
            emit_run extra source target distinct,List.reverse_cons,normalize_append_true,
            frame_eq_body,frameBody_append]
          simp only [frameBody,List.flatMap_cons,List.flatMap_nil,List.append_assoc,List.cons_append,List.nil_append]

theorem reversed_run (extra : Nat) (source target : Fin (extra+2)) (distinct : source ≠ target)
    (base : Fin (extra+2) → List Bool) (input suffix : List Bool) :
    Machine.run (step (reversedProgram extra source target)) (stripCost input+1)
      (reversedConfig extra source target 0 base input suffix) =
      some (reversedConfig extra source target 7 base [] (Encoding.frame (normalize input.reverse)++suffix)) := by
  have first : step (reversedProgram extra source target) (reversedConfig extra source target 0 base input suffix) =
      some (reversedConfig extra source target 1 base input (false::suffix)) := by
    simp [step,reversedProgram,reversedConfig,Ne.symm distinct]
    refine ⟨rfl,?_⟩
    funext r
    by_cases a : r=source
    · subst r; simp [distinct]
    · by_cases b : r=target
      · subst r; simp [Ne.symm distinct]
      · simp [a,b]
  rw [Machine.run,first,Option.bind_some,strip_run extra source target distinct]

theorem reversed_executes (extra : Nat) (source target : Fin (extra+2)) (distinct : source ≠ target)
    (store : Fin (extra+2) → List Bool) :
    Routine.Executes (Routine.ofProgram (reversedProgram extra source target)) store
      (stripCost (store source)+1)
      (Function.update (Function.update store source []) target
        (Encoding.frame (normalize (store source).reverse)++store target)) := by
  have start : reversedConfig extra source target 0 store (store source) (store target) =
      (⟨0,store⟩ : Config (reversedProgram extra source target)) := by
    apply congrArg (Config.mk _)
    funext r
    split_ifs <;> simp_all
  refine ⟨reversedConfig extra source target 7 store []
    (Encoding.frame (normalize (store source).reverse)++store target),?_,rfl,?_⟩
  · rw [← start]
    exact reversed_run extra source target distinct store (store source) (store target)
  · funext r
    dsimp only [reversedConfig]
    split_ifs <;> simp_all [Function.update]
    intro equal
    exact (distinct equal).elim

def formatRoutine (extra : Nat) (source target temporary : Fin (extra+3)) : Routine (extra+1) :=
  Routine.sequence
    (Routine.ofProgram (ListPrograms.reverseProgram (extra+1) source temporary))
    (Routine.ofProgram (reversedProgram (extra+1) temporary target))

def formatCost (bits : List Bool) : Nat := (2*bits.length+1)+1+(stripCost bits.reverse+1)

theorem formatCost_le (bits : List Bool) : formatCost bits ≤ 5*bits.length+4 := by
  have bound := stripCost_le bits.reverse
  simp only [List.length_reverse] at bound
  dsimp only [formatCost]
  omega

/-- A little-endian payload becomes the repository's canonical natural
frame. Source is consumed, empty temporary is restored, and other registers
are unchanged. Work is linear even for a zero with many redundant bits. -/
theorem format_executes (extra : Nat) (source target temporary : Fin (extra+3))
    (st : source ≠ target) (sw : source ≠ temporary) (tw : target ≠ temporary)
    (store : Fin (extra+3) → List Bool) (empty : store temporary = []) :
    Routine.Executes (formatRoutine extra source target temporary) store (formatCost (store source))
      (Function.update (Function.update store source []) target
        (Encoding.natural.encode (Encoding.value (store source))++store target)) := by
  let middle := Function.update (Function.update store source []) temporary (store source).reverse
  have reversed : Routine.Executes
      (Routine.ofProgram (ListPrograms.reverseProgram (extra+1) source temporary)) store
      (2*(store source).length+1) middle := by
    simpa +instances only [ListPrograms.reverseProgram,middle,empty,List.append_nil] using
      Routine.reverse_executes (extra+1) source temporary sw store
  have atSource : middle temporary = (store source).reverse := by simp only [middle,Function.update_self]
  have atTarget : middle target = store target := by
    simp only [middle,Function.update_of_ne tw,Function.update_of_ne (Ne.symm st)]
  have normalized := reversed_executes (extra+1) temporary target (Ne.symm tw) middle
  simp +instances only [reversedProgram] at normalized
  rw [atSource,atTarget,List.reverse_reverse,normalize_eq_bits] at normalized
  change Routine.Executes _ middle (stripCost (store source).reverse+1)
    (Function.update (Function.update middle temporary []) target
      (Encoding.natural.encode (Encoding.value (store source))++store target)) at normalized
  have restored : Function.update middle temporary [] = Function.update store source [] := by
    dsimp only [middle]
    rw [Function.update_idem]
    have unchanged : (Function.update store source []) temporary = [] := by
      rw [Function.update_of_ne (Ne.symm sw),empty]
    calc
      _ = Function.update (Function.update store source []) temporary
          ((Function.update store source []) temporary) :=
        congrArg (Function.update (Function.update store source []) temporary) unchanged.symm
      _ = _ := Function.update_eq_self _ _
  rw [restored] at normalized
  exact reversed.sequence normalized

end Counting.StackMachine.Normalize
