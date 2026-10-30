import Counting.StackRealizabilityMassFile
import Counting.StackDagIncrement

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def massPrepare : Routine 40 := sequence (ofProgram (ListPrograms.copyProgram 39 36 25 33))
  (DagValidation.incrementRoutine 39 0 25 2)

theorem massPrepare_executes (source weights level status child accumulator saved : List Bool)
    (query : Nat) :
    ∃ time ≤ 10*(query.size+1),
      Executes massPrepare (massFile source weights level [] query.bits status child accumulator saved) time
        (massFile source weights level (query+1).bits query.bits status child accumulator saved) := by
  let original := massFile source weights level [] query.bits status child accumulator saved
  have copying := copy_executes 39 36 25 33 (by decide) (by decide) (by decide) original
    (by simp [original,massFile])
  have queryAt : original 36=query.bits := by simp [original,massFile]
  have parentAt : original 25=[] := by simp [original,massFile]
  rw [queryAt,parentAt,List.append_nil,Encoding.bits_length] at copying
  let copied := Function.update original 25 query.bits
  obtain ⟨time,bound,incrementing⟩ := DagValidation.increment_natural 39 0 25 2
    (by decide) (by decide) (by decide) copied (by simp [copied,original,massFile])
    (by simp [copied,original,massFile]) query (by simp [copied])
  have final : Function.update copied 25 (query+1).bits=
      massFile source weights level (query+1).bits query.bits status child accumulator saved := by
    funext r
    fin_cases r <;> simp [copied,original,massFile]
  rw [final] at incrementing
  have execution := copying.sequence incrementing
  exact ⟨_,by omega,execution⟩

def massKeepSupply : Routine 40 := sequence (ofProgram (ListPrograms.copyProgram 39 26 37 33))
  (sequence (clear 26) (sequence (clear 25) (ofProgram (ListPrograms.copyProgram 39 36 25 33))))

theorem massKeepSupply_executes (source weights level status child : List Bool) (query supplied : Nat) :
    ∃ time ≤ 10*(query.size+supplied.size+1),
      Executes massKeepSupply
        (massFile source weights level (query+1).bits query.bits status child supplied.bits []) time
        (massFile source weights level query.bits query.bits status child [] supplied.bits) := by
  let original := massFile source weights level (query+1).bits query.bits status child supplied.bits []
  have copying := copy_executes 39 26 37 33 (by decide) (by decide) (by decide) original
    (by simp [original,massFile])
  have at26 : original 26=supplied.bits := by simp [original,massFile]
  have at37 : original 37=[] := by simp [original,massFile]
  rw [at26,at37,List.append_nil,Encoding.bits_length] at copying
  let copied := Function.update original 37 supplied.bits
  have clearAccumulator := clear_executes (26:Fin 42) copied
  have copied26 : copied 26=supplied.bits := by simp [copied,at26]
  rw [copied26,Encoding.bits_length] at clearAccumulator
  let noAccumulator := Function.update copied 26 []
  have clearParent := clear_executes (25:Fin 42) noAccumulator
  have no25 : noAccumulator 25=(query+1).bits := by simp [noAccumulator,copied,original,massFile]
  rw [no25,Encoding.bits_length] at clearParent
  let cleared := Function.update noAccumulator 25 []
  have parentCopy := copy_executes 39 36 25 33 (by decide) (by decide) (by decide) cleared
    (by simp [cleared,noAccumulator,copied,original,massFile])
  have clear36 : cleared 36=query.bits := by simp [cleared,noAccumulator,copied,original,massFile]
  have clear25 : cleared 25=[] := by simp [cleared]
  rw [clear36,clear25,List.append_nil,Encoding.bits_length] at parentCopy
  have final : Function.update cleared 25 query.bits=
      massFile source weights level query.bits query.bits status child [] supplied.bits := by
    funext r
    fin_cases r <;> simp [cleared,noAccumulator,copied,original,massFile]
  rw [final] at parentCopy
  have nextBits : (query+1).size ≤ query.size+1 := by
    have bound := DagValidation.increment_length_le query.bits
    simpa only [Machine.increment_bits,Encoding.bits_length] using bound
  have execution := copying.sequence (clearAccumulator.sequence (clearParent.sequence parentCopy))
  exact ⟨_,by omega,execution⟩

end Counting.StackMachine.RealizabilityCheck
