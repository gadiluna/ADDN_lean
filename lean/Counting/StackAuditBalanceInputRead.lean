import Counting.StackAuditPropagationInputRead

namespace Counting.StackMachine.AuditBalance
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

abbrev balanceInputWord := AuditPropagation.propagationInputWord

def balanceInputFile (input anchor code weights : List Bool) : Store 48 :=
  fun r=>if r=0 then input else if r=36 then anchor else if r=34 then code
    else if r=35 then weights else []

abbrev readBalanceInput : Routine 48 := sequence (ofProgram (unframeProgram 47 0 36 47))
  (sequence (ofProgram (unframeProgram 47 0 34 47)) (move 47 0 35 47))

/-- The complete encoded weight array is retained, including its actual
header. Only the two external frames are removed by the parser. -/
theorem readBalanceInput_executes (anchor : Nat) (vista : Executable.Vista) (weights : Array Nat) :
    ∃ time ≤ 100*((balanceInputWord anchor vista weights).length+1)^2,
      Executes readBalanceInput
        (balanceInputFile (balanceInputWord anchor vista weights) [] [] []) time
        (balanceInputFile [] anchor.bits (Encoding.vista.encode vista)
          ((Encoding.array Encoding.natural).encode weights)) := by
  let code:=Encoding.vista.encode vista
  let values:=(Encoding.array Encoding.natural).encode weights
  let initial:=balanceInputFile (balanceInputWord anchor vista weights) [] [] []
  let first:=balanceInputFile (Encoding.frame code++values) anchor.bits [] []
  have a:=unframe_canonical_executes 47 (0:Fin 50) 36 47 (by decide) (by decide) (by decide)
    initial anchor.bits (Encoding.frame code++values) rfl rfl
  have aResult : Function.update (Function.update initial 0 (Encoding.frame code++values)) 36
      (anchor.bits++initial 36)=first := by
    funext r;fin_cases r <;> simp [initial,first,balanceInputFile]
  rw [aResult] at a
  let second:=balanceInputFile values anchor.bits code []
  have b:=unframe_canonical_executes 47 (0:Fin 50) 34 47 (by decide) (by decide) (by decide)
    first code values rfl rfl
  have bResult : Function.update (Function.update first 0 values) 34 (code++first 34)=second := by
    funext r;fin_cases r <;> simp [first,second,balanceInputFile]
  rw [bResult] at b
  have c:=move_executes 47 (0:Fin 50) 35 47 (by decide) (by decide) (by decide) second rfl
  have cResult : Function.update (Function.update second 35 (second 0++second 35)) 0 []=
      balanceInputFile [] anchor.bits code values := by
    funext r;fin_cases r <;> simp [second,balanceInputFile]
  rw [cResult] at c
  change Executes _ second (6*values.length+4) _ at c
  have inputLength : (balanceInputWord anchor vista weights).length=
      2*anchor.size+1+(2*code.length+1)+values.length := by
    simp only [balanceInputWord,AuditPropagation.propagationInputWord,
      AuditPropagation.propagationInputCodec,Encoding.product,Encoding.framed,
      List.length_append,Encoding.natural_length,Encoding.frame_length,code,values]
    omega
  have linear : (balanceInputWord anchor vista weights).length+1 ≤
      ((balanceInputWord anchor vista weights).length+1)^2 := Nat.le_self_pow (by decide) _
  refine ⟨_,?_,a.sequence (b.sequence c)⟩
  simp only [Encoding.bits_length]
  omega

end Counting.StackMachine.AuditBalance
