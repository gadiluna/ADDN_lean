import Counting.StackRoutineUnary
import Counting.StackRoutineLists
import Counting.StackUnaryPower
import Counting.StackEncodingFrame

namespace Counting.StackMachine.Routine

/-- Roles: unary source, output, copied counter, binary payload, scratch.
Emit the canonical binary natural codec while preserving the source. -/
def emitNatural (extra : Nat) (w : PowerWorkspace extra) : Routine (extra+3) :=
  sequence (ofProgram (ListPrograms.copyProgram (extra+2) (w 0) (w 2) (w 4)))
    (sequence (ofProgram (Unary.toBinaryProgram (extra+2) (w 2) (w 3) (w 4)))
      (EncodingPrograms.frameRoutine (extra+2) (w 3) (w 1) (w 4)))

/-- This emitter executes on the compact binary output tape. The work bound
is polynomial in the length of the supplied unary counter, and all scratch
registers are restored to empty. -/
theorem emitNatural_executes (extra : Nat) (w : PowerWorkspace extra)
    (store : Fin (extra+5) → List Bool) (counterEmpty : store (w 2) = [])
    (binaryEmpty : store (w 3) = []) (workEmpty : store (w 4) = []) :
    ∃ transitions ≤ 20*((store (w 0)).length+1)^2,
      Executes (emitNatural extra w) store transitions
        (Function.update store (w 1) (Encoding.natural.encode (store (w 0)).length++store (w 1))) := by
  let copied := Function.update store (w 2) (store (w 0))
  have copy : Executes (ofProgram (ListPrograms.copyProgram (extra+2) (w 0) (w 2) (w 4))) store
      (5*(store (w 0)).length+2) copied := by
    obtain ⟨finish,run,halted,finalStore⟩ := copy_executes (extra+2) (w 0) (w 2) (w 4)
      (workspace_ne w (by decide)) (workspace_ne w (by decide)) (workspace_ne w (by decide)) store workEmpty
    refine ⟨finish,run,halted,?_⟩
    rw [finalStore]
    funext register
    by_cases equal : register = w 2
    · subst register; simp [copied,counterEmpty]
    · simp [copied,Function.update,equal]
      intro same
      exact False.elim (equal same)
  obtain ⟨convertTime,convertBound,convertedRun⟩ := toBinary_executes (extra+2) (w 2) (w 3) (w 4)
    (workspace_ne w (by decide)) (workspace_ne w (by decide)) (workspace_ne w (by decide)) copied 0
    (by simp [copied,w.injective.eq_iff,binaryEmpty])
    (by simp [copied,w.injective.eq_iff,workEmpty])
  let converted := Function.update (Function.update copied (w 2) []) (w 3) (store (w 0)).length.bits
  have conversion : Executes (ofProgram (Unary.toBinaryProgram (extra+2) (w 2) (w 3) (w 4))) copied
      convertTime converted := by
    obtain ⟨finish,run,halted,finalStore⟩ := convertedRun
    refine ⟨finish,run,halted,?_⟩
    rw [finalStore]
    funext register
    by_cases equal : register = w 3
    · subst register; simp [converted,copied]
    · simp [converted,Function.update,equal]
      exact (if_neg equal).symm
  have convertedBits : converted (w 3) = (store (w 0)).length.bits := by simp [converted]
  have framed := EncodingPrograms.frame_executes (extra+2) (w 3) (w 1) (w 4)
    (workspace_ne w (by decide)) (workspace_ne w (by decide)) (workspace_ne w (by decide)) converted
    (by simp [converted,copied,w.injective.eq_iff,workEmpty])
  have combined := copy.sequence (conversion.sequence framed)
  refine ⟨5*(store (w 0)).length+2+1+(convertTime+1+(5*(converted (w 3)).length+4)),?_,?_⟩
  · have bitsBound : (store (w 0)).length.size ≤ (store (w 0)).length :=
      Nat.size_le.mpr Nat.lt_two_pow_self
    simp only [copied,Function.update_self,Nat.zero_add] at convertBound
    rw [convertedBits,Encoding.bits_length]
    nlinarith
  · have finalStore : EncodingPrograms.frameResult (extra+2) (w 3) (w 1) (w 4) converted =
        Function.update store (w 1) (Encoding.natural.encode (store (w 0)).length++store (w 1)) := by
      funext register
      by_cases binary : register = w 3
      · subst register
        simp [EncodingPrograms.frameResult,w.injective.eq_iff,binaryEmpty]
      · by_cases output : register = w 1
        · subst register
          simp [EncodingPrograms.frameResult,converted,copied,w.injective.eq_iff,Encoding.natural]
        · by_cases scratch : register = w 4
          · subst register
            simp [EncodingPrograms.frameResult,w.injective.eq_iff,workEmpty]
          · by_cases counter : register = w 2
            · subst register
              simp [EncodingPrograms.frameResult,converted,copied,w.injective.eq_iff,counterEmpty]
            · simp [EncodingPrograms.frameResult,converted,copied,binary,output,scratch,counter]
    rw [finalStore] at combined
    exact combined

end Counting.StackMachine.Routine
