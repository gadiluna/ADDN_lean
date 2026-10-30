import Counting.StackDagAddCountEmit
import Counting.StackUnframeCanonical

namespace Counting.StackMachine.DagUpdate
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

def readCurrent (extra : Nat) (w : AddWorkspace extra) : Routine (extra+18) :=
  sequence (ofProgram (unframeProgram (extra+17) (w 0) (w 6) (w 19)))
    (ofProgram (unframeProgram (extra+17) (w 0) (w 7) (w 19)))

/-- Parse the next sparse pair; natural counts remain canonical binary
payloads, and the untouched suffix is available to the next iteration. -/
theorem readCurrent_executes (extra : Nat) (w : AddWorkspace extra) (store : Store (extra+18))
    (i c : Nat) (suffix : List Bool)
    (source : store (w 0)=(Encoding.product Encoding.natural Encoding.natural).encode (i,c)++suffix)
    (firstEmpty : store (w 6)=[]) (secondEmpty : store (w 7)=[]) (scratch : store (w 19)=[]) :
    Executes (readCurrent extra w) store (5*(i.bits.length+c.bits.length)+5)
      (Function.update (Function.update (Function.update store (w 0) suffix) (w 6) i.bits) (w 7) c.bits) := by
  have ne (a b : Fin 20) (different : a≠b) : w a≠w b := fun equal=>different (w.injective equal)
  have first:=unframe_canonical_executes (extra+17) (w 0) (w 6) (w 19)
    (ne 0 6 (by decide)) (ne 0 19 (by decide)) (ne 6 19 (by decide)) store
    i.bits (Encoding.frame c.bits++suffix)
    (by simpa only [Encoding.product,Encoding.natural,List.append_assoc] using source) scratch
  rw [firstEmpty,List.append_nil] at first
  let read:=Function.update (Function.update store (w 0) (Encoding.frame c.bits++suffix)) (w 6) i.bits
  have second:=unframe_canonical_executes (extra+17) (w 0) (w 7) (w 19)
    (ne 0 7 (by decide)) (ne 0 19 (by decide)) (ne 7 19 (by decide)) read
    c.bits suffix (by simp [read,w.injective.eq_iff]) (by simp [read,w.injective.eq_iff,scratch])
  have target : read (w 7)=[] := by simp [read,w.injective.eq_iff,secondEmpty]
  rw [target,List.append_nil] at second
  have final : Function.update (Function.update read (w 0) suffix) (w 7) c.bits=
      Function.update (Function.update (Function.update store (w 0) suffix) (w 6) i.bits) (w 7) c.bits := by
    funext r
    by_cases a : r=w 0
    · subst r;simp [read,w.injective.eq_iff]
    · simp [read,Function.update_apply,a]
  rw [final] at second
  simpa only [readCurrent,show 5*i.bits.length+2+1+(5*c.bits.length+2)=5*(i.bits.length+c.bits.length)+5 by omega]
    using first.sequence second

end Counting.StackMachine.DagUpdate
