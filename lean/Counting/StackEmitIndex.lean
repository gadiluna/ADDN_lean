import Counting.StackEmitNatural
import Counting.StackRoutineFixedPrefix

namespace Counting.StackMachine.Routine

/-- Emit a binary index from the internal unary representation `index+1`.
The nonempty source and every other input register are preserved. -/
def emitIndex (extra : Nat) (w : PowerWorkspace extra) : Routine (extra+3) :=
  sequence (discardBit (w 0))
    (sequence (emitNatural extra w) (pushBit (w 0) true))

theorem emitIndex_executes (extra : Nat) (w : PowerWorkspace extra)
    (store : Fin (extra+5) → List Bool) (index : Nat)
    (source : store (w 0)=List.replicate (index+1) true)
    (counterEmpty : store (w 2)=[]) (binaryEmpty : store (w 3)=[])
    (workEmpty : store (w 4)=[]) :
    ∃ transitions ≤ 24*(index+1)^2,
      Executes (emitIndex extra w) store transitions
        (Function.update store (w 1) (Encoding.natural.encode index++store (w 1))) := by
  let shortened := Function.update store (w 0) (List.replicate index true)
  have discard : Executes (discardBit (w 0)) store 1 shortened := by
    simpa only [source,List.replicate_succ,List.tail_cons,shortened]
      using discardBit_executes (w 0) store
  obtain ⟨time,bounded,emitted⟩ := emitNatural_executes extra w shortened
    (by simp [shortened,w.injective.eq_iff,counterEmpty])
    (by simp [shortened,w.injective.eq_iff,binaryEmpty])
    (by simp [shortened,w.injective.eq_iff,workEmpty])
  have shortenedLength : (shortened (w 0)).length=index := by simp [shortened]
  have shortenedOutput : shortened (w 1)=store (w 1) := by
    simp [shortened,w.injective.eq_iff]
  rw [shortenedLength,shortenedOutput] at emitted
  rw [shortenedLength] at bounded
  let output := Function.update shortened (w 1) (Encoding.natural.encode index++store (w 1))
  have restore := pushBit_executes (w 0) true output
  have restored : Function.update output (w 0) (true::output (w 0))=
      Function.update store (w 1) (Encoding.natural.encode index++store (w 1)) := by
    funext register
    by_cases first : register=w 0
    · subst register
      simp [output,shortened,w.injective.eq_iff,source,List.replicate_succ]
    · simp [output,shortened,Function.update,first]
  rw [restored] at restore
  refine ⟨1+1+(time+1+1),?_,discard.sequence (emitted.sequence restore)⟩
  have positive : 0 < (index+1)^2 := by positivity
  omega

end Counting.StackMachine.Routine
