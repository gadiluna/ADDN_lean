import Counting.MachinePositiveNaturals
import Counting.StackRoutineIsolateHalt
import Counting.StackEncodingBranch

namespace Counting.StackMachine.AuditPositive
open Routine EncodingPrograms

/-- Canonical solver output, including failure, as actually serialized. -/
def inputWord (values : Option (Array Rat)) : List Bool :=
  (Encoding.optional Encoding.rationalRow).encode (values.map Array.toList)

/-- Precisely the first two option binds in `Executable.auditSuffix?`. -/
def result (values : Option (Array Rat)) : Option (Array Nat) :=
  values.bind Executable.positiveNaturals?

def outputWord (values : Option (Array Rat)) : List Bool :=
  (Encoding.optional (Encoding.array Encoding.natural)).encode (result values)

/-- The tag is physically consumed. A successful solver result is processed
by the existing vector conversion, including erasure of private registers. -/
abbrev routine : Routine 30 :=
  branchRoutine 0 (isolate PositiveNaturals.complete) (pushBit 1 false)

private theorem popped (tag : Bool) (word : List Bool) :
    Function.update (inputStore 30 (tag::word)) 0 word=inputStore 30 word := by
  funext r
  by_cases equal : r=0
  · subst r;simp [inputStore]
  · simp [inputStore,equal]

theorem routine_executes (values : Option (Array Rat)) :
    ∃ time ≤ 400000*((inputWord values).length+1)^3,
      Executes routine (inputStore 30 (inputWord values)) time
        (outputStore 30 (outputWord values)) := by
  cases values with
  | none =>
    have a := pushBit_executes (1:Fin 32) false (inputStore 30 [])
    have updated : Function.update (inputStore 30 []) 1 (false::inputStore 30 [] 1)=
        outputStore 30 [false] := by
      funext r
      by_cases equal : r=1
      · subst r;simp [inputStore,outputStore]
      · simp [inputStore,outputStore,equal]
    rw [updated] at a
    have b := branch_executes_false (0:Fin 32) (isolate PositiveNaturals.complete) (pushBit 1 false)
      (inputStore 30 [false]) (outputStore 30 [false]) [] 1 rfl (by rw [popped];exact a)
    exact ⟨2,by simp [inputWord,Encoding.optional],b⟩
  | some values =>
    let word := Encoding.rationalRow.encode values.toList
    obtain ⟨time,bounded,ran⟩ := isolate_halts PositiveNaturals.complete word
      (Counting.PositiveNaturals.output values.toList) (10000*(word.length+1)^3)
      (PositiveNaturals.complete_halts values.toList)
    rw [Counting.PositiveNaturals.output_executable] at ran
    simp only [Array.toArray_toList] at ran
    have b := branch_executes_true (0:Fin 32) (isolate PositiveNaturals.complete) (pushBit 1 false)
      (inputStore 30 (true::word)) _ word time rfl (by rw [popped];exact ran)
    refine ⟨1+time,?_,b⟩
    have linear : word.length+1≤(word.length+1)^3 := Nat.le_self_pow (by decide) _
    have positive : 1≤(word.length+1)^3 := Nat.one_le_pow' 3 word.length
    have larger : (word.length+1)^3≤(word.length+2)^3 := Nat.pow_le_pow_left (by omega) 3
    change time≤33*(10000*(word.length+1)^3+word.length+3) at bounded
    change 1+time≤400000*((true::word).length+1)^3
    change 1+time≤400000*(word.length+2)^3
    omega

theorem routine_halts (values : Option (Array Rat)) :
    ∃ time last,time≤400000*((inputWord values).length+1)^3 ∧
      HaltsAt routine.program (inputWord values) time last ∧
      last.store 1=outputWord values := by
  obtain ⟨time,bounded,last,ran,halted,stored⟩ := routine_executes values
  exact ⟨time,last,bounded,⟨ran,halted⟩,by rw [stored];rfl⟩

/-- The output cannot grow beyond the encoded solver result by more than one bit. -/
theorem output_length (values : Option (Array Rat)) :
    (outputWord values).length≤(inputWord values).length+1 := by
  cases values with
  | none => simp [outputWord,result,inputWord,Encoding.optional]
  | some values =>
    have bound := PositiveNaturals.output_length_le values.toList
    rw [Counting.PositiveNaturals.output_executable] at bound
    simpa [inputWord,outputWord,result,Encoding.optional] using bound.trans
      (show (Encoding.rationalRow.encode values.toList).length+1≤
        (Encoding.rationalRow.encode values.toList).length+2 by omega)

/-- Failure of this concrete conversion is exactly an early rejection in the
actual audit continuation. -/
theorem failed_conversion_rejects (vista : Executable.Vista) (candidate last anchor : Nat)
    (values : Option (Array Rat)) (failure : result values=none) :
    Executable.auditSuffix? vista candidate last anchor values=none := by
  cases values with
  | none => rfl
  | some values =>
    change Executable.positiveNaturals? values=none at failure
    simp [Executable.auditSuffix?,failure]

end Counting.StackMachine.AuditPositive
