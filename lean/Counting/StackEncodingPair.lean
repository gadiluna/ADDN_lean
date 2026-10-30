import Counting.StackEncodingFlaggedCorrectness

namespace Counting.StackMachine.EncodingPrograms

set_option backward.isDefEq.respectTransparency false

/-- Replace the top two status bits by their conjunction. -/
def combineFlagsProgram (extra : Nat) (flag : Fin (extra+2)) : Program where
  extraRegisters := extra
  states := 5
  code control := match control.val with
    | 0 => .pop flag 3 1 2
    | 1 => .pop flag 3 3 3
    | 2 => .pop flag 3 3 4
    | 3 => .push flag false 5
    | 4 => .push flag true 5
    | _ => .halt

theorem combineFlags_run (extra : Nat) (flag : Fin (extra+2))
    (store : Fin (extra+2) → List Bool) (first second : Bool) (tail : List Bool) :
    Machine.run (step (combineFlagsProgram extra flag)) 3
      ⟨0,Function.update store flag (second::first::tail)⟩ =
      some ⟨5,Function.update store flag ((first && second)::tail)⟩ := by
  cases first <;> cases second <;>
    dsimp [Machine.run, step, combineFlagsProgram] <;>
    simp [Function.update_idem]

theorem combineFlags_executes (extra : Nat) (flag : Fin (extra+2))
    (store : Fin (extra+2) → List Bool) (first second : Bool) (tail : List Bool)
    (status : store flag = second::first::tail) :
    Routine.Executes (Routine.ofProgram (combineFlagsProgram extra flag)) store 3
      (Function.update store flag ((first && second)::tail)) := by
  have start : Function.update store flag (second::first::tail) = store := by
    rw [←status, Function.update_eq_self]
  refine ⟨⟨5,_⟩,?_,rfl,rfl⟩
  have executed := combineFlags_run extra flag store first second tail
  rw [start] at executed
  exact executed

def pairFirst (extra : Nat) (regs : Fin 5 → Fin (extra+5))
    (store : Fin (extra+5) → List Bool) : Fin (extra+5) → List Bool :=
  flaggedResult (extra+1) (regs 0) (regs 1) (regs 3) (regs 4) store

def pairSecond (extra : Nat) (regs : Fin 5 → Fin (extra+5))
    (store : Fin (extra+5) → List Bool) : Fin (extra+5) → List Bool :=
  flaggedResult (extra+1) (regs 0) (regs 2) (regs 3) (regs 4) (pairFirst extra regs store)

def pairResult (extra : Nat) (regs : Fin 5 → Fin (extra+5))
    (store : Fin (extra+5) → List Bool) : Fin (extra+5) → List Bool :=
  Function.update (pairSecond extra regs store) (regs 4)
    (((Encoding.unframe (store (regs 0))).isSome &&
      (Encoding.unframe (pairFirst extra regs store (regs 0))).isSome)::store (regs 4))

/-- Registers are source, first payload, second payload, scratch, status.
No branch evaluates a Lean decoder: both parsers and the conjunction are
finite stack programs, and all sequencing jumps are counted. -/
def pairRoutine (extra : Nat) (regs : Fin 5 → Fin (extra+5)) : Routine (extra+3) :=
  Routine.sequence
    (Routine.sequence
      (Routine.ofProgram (flaggedProgram (extra+1) (regs 0) (regs 1) (regs 3) (regs 4)))
      (Routine.ofProgram (flaggedProgram (extra+1) (regs 0) (regs 2) (regs 3) (regs 4))))
    (Routine.ofProgram (combineFlagsProgram (extra+3) (regs 4)))

theorem flagged_result_source_length (extra : Nat) (source target temporary flag : Fin (extra+4))
    (fs : flag≠source) (store : Fin (extra+4) → List Bool) :
    (flaggedResult extra source target temporary flag store source).length ≤ (store source).length := by
  unfold flaggedResult
  cases parsed : Encoding.unframe (store source) with
  | none => simp [parserStore, Ne.symm fs]
  | some pair =>
    obtain ⟨payload,suffix⟩:=pair
    have split := Machine.unframe_sound (store source) payload suffix parsed
    simp only [Function.update_of_ne (Ne.symm fs), parserStore, ite_true]
    rw [split, List.length_append]
    omega

/-- Total full-store execution, including all failure paths. Only the input
length enters this cost bound; arbitrary preexisting data in other registers
are preserved or extended as specified by `pairResult`. -/
theorem pair_executes (extra : Nat) (regs : Fin 5 → Fin (extra+5))
    (distinct : Function.Injective regs) (store : Fin (extra+5) → List Bool)
    (scratch : store (regs 3)=[]) :
    ∃ time ≤ 6*(store (regs 0)).length+13,
      Routine.Executes (pairRoutine extra regs) store time (pairResult extra regs store) := by
  have ne : ∀ i j : Fin 5, i≠j → regs i≠regs j := fun i j neq same => neq (distinct same)
  obtain ⟨firstTime,firstBound,firstRun⟩ := flagged_executes (extra+1) (regs 0) (regs 1) (regs 3) (regs 4)
    (ne 0 1 (by decide)) (ne 0 3 (by decide)) (ne 1 3 (by decide))
    (ne 4 0 (by decide)) (ne 4 1 (by decide)) (ne 4 3 (by decide)) store scratch
  have firstScratch : pairFirst extra regs store (regs 3)=[] := flagged_result_scratch (extra+1)
    (regs 0) (regs 1) (regs 3) (regs 4) (ne 0 3 (by decide)) (ne 1 3 (by decide)) (ne 4 3 (by decide)) store
  obtain ⟨secondTime,secondBound,secondRun⟩ := flagged_executes (extra+1) (regs 0) (regs 2) (regs 3) (regs 4)
    (ne 0 2 (by decide)) (ne 0 3 (by decide)) (ne 2 3 (by decide))
    (ne 4 0 (by decide)) (ne 4 2 (by decide)) (ne 4 3 (by decide)) (pairFirst extra regs store) firstScratch
  have sourceBound : (pairFirst extra regs store (regs 0)).length ≤ (store (regs 0)).length :=
    flagged_result_source_length (extra+1) (regs 0) (regs 1) (regs 3) (regs 4) (ne 4 0 (by decide)) store
  have status : pairSecond extra regs store (regs 4) =
      (Encoding.unframe (pairFirst extra regs store (regs 0))).isSome::
        (Encoding.unframe (store (regs 0))).isSome::store (regs 4) := by
    rw [pairSecond, flagged_result_flag, pairFirst, flagged_result_flag]
  have combineRun := combineFlags_executes (extra+3) (regs 4) (pairSecond extra regs store)
    (Encoding.unframe (store (regs 0))).isSome
    (Encoding.unframe (pairFirst extra regs store (regs 0))).isSome (store (regs 4)) status
  refine ⟨(firstTime+1+secondTime)+1+3, by omega, ?_⟩
  exact (firstRun.sequence secondRun).sequence combineRun

end Counting.StackMachine.EncodingPrograms
