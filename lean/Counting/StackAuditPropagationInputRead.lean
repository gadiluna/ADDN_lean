import Counting.StackUnframeCanonical
import Counting.StackRoutineMove
import Counting.StackRoutineBasic
import Counting.EncodingRationalRows
import Counting.EncodingNetwork

namespace Counting.StackMachine.AuditPropagation
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

def propagationInputCodec : Encoding.Codec (Nat×Executable.Vista×Array Nat) :=
  Encoding.product Encoding.natural
    (Encoding.product (Encoding.framed Encoding.vista) (Encoding.array Encoding.natural))

def propagationInputWord (anchor : Nat) (vista : Executable.Vista) (values : Array Nat) : List Bool :=
  propagationInputCodec.encode (anchor,vista,values)

def propagationInputFile (input anchor code values header : List Bool) : Store 42 :=
  fun r=>if r=0 then input else if r=42 then anchor else if r=34 then code
    else if r=36 then values else if r=2 then header else []

abbrev readPropagationInput : Routine 42 := sequence (ofProgram (unframeProgram 41 0 42 43))
  (sequence (ofProgram (unframeProgram 41 0 34 43))
    (sequence (ofProgram (unframeProgram 41 0 2 43))
      (sequence (clear 2) (move 41 0 36 43))))

/-- Read the anchor and framed vista, then discard only the actual array
header. The values remain a binary stream; no value is expanded into unary. -/
theorem readPropagationInput_executes (anchor : Nat) (vista : Executable.Vista) (values : Array Nat) :
    ∃ time ≤ 100*((propagationInputWord anchor vista values).length+1)^2,
      Executes readPropagationInput
        (propagationInputFile (propagationInputWord anchor vista values) [] [] [] []) time
        (propagationInputFile [] anchor.bits (Encoding.vista.encode vista)
          (Encoding.sequence Encoding.natural values.toList) []) := by
  let code:=Encoding.vista.encode vista
  let payload:=Encoding.sequence Encoding.natural values.toList
  let arrayWord:=(Encoding.array Encoding.natural).encode values
  let initial:=propagationInputFile (propagationInputWord anchor vista values) [] [] [] []
  let first:=propagationInputFile (Encoding.frame code++arrayWord) anchor.bits [] [] []
  have a:=unframe_canonical_executes 41 (0:Fin 44) 42 43 (by decide) (by decide) (by decide)
    initial anchor.bits (Encoding.frame code++arrayWord) rfl rfl
  have aResult : Function.update (Function.update initial 0 (Encoding.frame code++arrayWord)) 42
      (anchor.bits++initial 42)=first := by
    funext r;fin_cases r <;> simp [initial,first,propagationInputFile]
  rw [aResult] at a
  let second:=propagationInputFile arrayWord anchor.bits code [] []
  have b:=unframe_canonical_executes 41 (0:Fin 44) 34 43 (by decide) (by decide) (by decide)
    first code arrayWord rfl rfl
  have bResult : Function.update (Function.update first 0 arrayWord) 34 (code++first 34)=second := by
    funext r;fin_cases r <;> simp [first,second,propagationInputFile]
  rw [bResult] at b
  let third:=propagationInputFile payload anchor.bits code [] values.size.bits
  have c:=unframe_canonical_executes 41 (0:Fin 44) 2 43 (by decide) (by decide) (by decide)
    second values.size.bits payload (by
      simp only [second,propagationInputFile,ite_true]
      simp only [arrayWord,Encoding.array,Encoding.transport,Encoding.list,
        Encoding.natural,Array.length_toList,payload]) rfl
  have cResult : Function.update (Function.update second 0 payload) 2 (values.size.bits++second 2)=third := by
    funext r;fin_cases r <;> simp [second,third,propagationInputFile]
  rw [cResult] at c
  let cleared:=propagationInputFile payload anchor.bits code [] []
  have d:=clear_executes (2:Fin 44) third
  have dResult : Function.update third 2 []=cleared := by
    funext r;fin_cases r <;> simp [third,cleared,propagationInputFile]
  rw [dResult] at d
  change Executes _ third (values.size.bits.length+1) cleared at d
  have e:=move_executes 41 (0:Fin 44) 36 43 (by decide) (by decide) (by decide) cleared rfl
  have eResult : Function.update (Function.update cleared 36 (cleared 0++cleared 36)) 0 []=
      propagationInputFile [] anchor.bits code payload [] := by
    funext r;fin_cases r <;> simp [cleared,propagationInputFile]
  rw [eResult] at e
  change Executes _ cleared (6*payload.length+4) _ at e
  have inputLength : (propagationInputWord anchor vista values).length=
      2*anchor.size+1+(2*code.length+1)+(2*values.size.size+1)+payload.length := by
    simp only [propagationInputWord,propagationInputCodec,Encoding.product,Encoding.framed,
      List.length_append,Encoding.natural_length,Encoding.frame_length,
      Encoding.array,Encoding.transport,Encoding.list,Array.length_toList,code,payload]
    omega
  refine ⟨_,?_,a.sequence (b.sequence (c.sequence (d.sequence e)))⟩
  simp only [Encoding.bits_length]
  have linear : (propagationInputWord anchor vista values).length+1 ≤
      ((propagationInputWord anchor vista values).length+1)^2 := Nat.le_self_pow (by decide) _
  omega

end Counting.StackMachine.AuditPropagation
