import Counting.ExternalCoefficientEmit
import Counting.StackRoutineUnary

namespace Counting.External.CoefficientMachine
open StackMachine StackMachine.Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

def headerScratch : List (Fin 64) := [20,26,55,56]
def emitCoefficientHeader (extra : Nat) (w : Workspace extra) : Routine (extra+62) :=
  sequence (ofProgram (ListPrograms.copyProgram (extra+61) (w 25) (w 26) (w 20)))
    (sequence (pushBit (w 26) true)
      (sequence (ofProgram (Unary.toBinaryProgram (extra+61) (w 26) (w 55) (w 20)))
        (emitCoefficient extra w)))

theorem emitCoefficientHeader_executes (extra : Nat) (w : Workspace extra)
    (store : Fin (extra+64) → List Bool) (empty : ∀ i∈headerScratch,store (w i)=[]) :
    ∃ time ≤ 100*((store (w 25)).length+2)^2,
      Executes (emitCoefficientHeader extra w) store time
        (Function.update store (w 36)
          ((Encoding.natural.encode ((store (w 25)).length+1)).reverse++store (w 36))) := by
  have copying:=copy_executes (extra+61) (w 25) (w 26) (w 20)
    (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) store (empty 20 (by decide))
  rw [empty 26 (by decide),List.append_nil] at copying
  let copied:=Function.update store (w 26) (store (w 25))
  have pushing:=pushBit_executes (w 26) true copied
  let incremented:=Function.update store (w 26) (true::store (w 25))
  have pushingAs : Executes (pushBit (w 26) true) copied 1 incremented := by
    simpa [copied,incremented,Function.update_idem] using pushing
  obtain ⟨convertTime,convertBound,converting⟩:=toBinary_executes (extra+61) (w 26) (w 55) (w 20)
    (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) incremented 0
    (by simp [incremented,w.injective.eq_iff,empty,headerScratch])
    (by simp [incremented,w.injective.eq_iff,empty,headerScratch])
  have counterAt : (incremented (w 26)).length=(store (w 25)).length+1 := by simp [incremented]
  rw [counterAt,Nat.zero_add] at convertBound converting
  let binary:=Function.update store (w 55) ((store (w 25)).length+1).bits
  have converted : Function.update (Function.update incremented (w 26) []) (w 55)
      ((store (w 25)).length+1).bits=binary := by
    funext r
    by_cases e26 : r=w 26
    · subst r;simp [binary,w.injective.eq_iff,empty,headerScratch]
    · simp [binary,incremented,Function.update_apply,e26]
  rw [converted] at converting
  have emitting:=emitCoefficient_executes extra w binary ((store (w 25)).length+1) (by simp [binary])
    (by simp [binary,w.injective.eq_iff,empty,headerScratch])
    (by simp [binary,w.injective.eq_iff,empty,headerScratch])
  have final : Function.update (Function.update binary (w 55) []) (w 36)
      ((Encoding.natural.encode ((store (w 25)).length+1)).reverse++binary (w 36))=
      Function.update store (w 36)
      ((Encoding.natural.encode ((store (w 25)).length+1)).reverse++store (w 36)) := by
    funext r
    by_cases e55 : r=w 55
    · subst r;simp [w.injective.eq_iff,empty,headerScratch]
    · simp [binary,Function.update_apply,e55,w.injective.eq_iff]
  rw [final] at emitting
  refine ⟨5*(store (w 25)).length+2+1+(1+1+(convertTime+1+(9*((store (w 25)).length+1).bits.length+8))),?_,
    copying.sequence (pushingAs.sequence (converting.sequence emitting))⟩
  have size : ((store (w 25)).length+1).bits.length≤(store (w 25)).length+1 := by
    rw [Encoding.bits_length_le_iff];exact Nat.lt_two_pow_self
  nlinarith

end Counting.External.CoefficientMachine
