import Counting.ExternalCoefficientTriple
import Counting.StackEncodingFrame

namespace Counting.External.CoefficientMachine
open StackMachine StackMachine.Routine StackMachine.EncodingPrograms
set_option backward.isDefEq.respectTransparency false

def emitCoefficient (extra : Nat) (w : Workspace extra) : Routine (extra+62) :=
  sequence (frameRoutine (extra+61) (w 55) (w 56) (w 20))
    (ofProgram (ListPrograms.reverseProgram (extra+62) (w 56) (w 36)))

theorem emitCoefficient_executes (extra : Nat) (w : Workspace extra) (store : Fin (extra+64) → List Bool)
    (value : Nat) (input : store (w 55)=value.bits) (buffer : store (w 56)=[]) (scratch : store (w 20)=[]) :
    Executes (emitCoefficient extra w) store (9*value.bits.length+8)
      (Function.update (Function.update store (w 55) []) (w 36)
        ((Encoding.natural.encode value).reverse++store (w 36))) := by
  have framing:=frame_executes (extra+61) (w 55) (w 56) (w 20)
    (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) store scratch
  rw [input] at framing
  let framed:=Function.update (Function.update store (w 55) []) (w 56) (Encoding.natural.encode value)
  have frameFinal : frameResult (extra+61) (w 55) (w 56) (w 20) store=framed := by
    funext r
    by_cases e55 : r=w 55
    · subst r;simp [framed,frameResult,w.injective.eq_iff]
    · by_cases e56 : r=w 56
      · subst r;simp [framed,frameResult,w.injective.eq_iff,input,buffer,Encoding.natural]
      · by_cases e20 : r=w 20
        · subst r;simp [framed,frameResult,w.injective.eq_iff,scratch]
        · simp [framed,frameResult,e55,e56,e20]
  rw [frameFinal] at framing
  have reversing:=reverse_executes (extra+62) (w 56) (w 36) (by simp [w.injective.eq_iff]) framed
  have sourceAt : framed (w 56)=Encoding.natural.encode value := by simp [framed]
  have outputAt : framed (w 36)=store (w 36) := by simp [framed,w.injective.eq_iff]
  rw [sourceAt,outputAt] at reversing
  have final : Function.update (Function.update framed (w 56) []) (w 36)
      ((Encoding.natural.encode value).reverse++store (w 36))=
      Function.update (Function.update store (w 55) []) (w 36)
      ((Encoding.natural.encode value).reverse++store (w 36)) := by
    funext r
    by_cases e56 : r=w 56
    · subst r;simp [w.injective.eq_iff,buffer]
    · simp [framed,Function.update_apply,e56]
  rw [final] at reversing
  have composed:=framing.sequence reversing
  simpa only [emitCoefficient,Encoding.natural,Encoding.frame_length,show 5*value.bits.length+4+1+(2*(2*value.bits.length+1)+1)=9*value.bits.length+8 by omega] using composed

end Counting.External.CoefficientMachine
