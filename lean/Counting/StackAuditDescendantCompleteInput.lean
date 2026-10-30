import Counting.StackUnframeCanonical
import Counting.StackRoutineMove
import Counting.StackRoutineClean
import Counting.EncodingNetwork

namespace Counting.StackMachine.AuditDescendant
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

def completeInputWord (vista : Executable.Vista) (weights : Array Nat) (anchor last : Nat) : List Bool :=
  Encoding.natural.encode anchor++Encoding.natural.encode last++Encoding.frame (Encoding.vista.encode vista)++
    (Encoding.array Encoding.natural).encode weights

def completeInputFile (source anchor last code weights : List Bool) : Store 46 := fun r=>
  if r=0 then source else if r=40 then anchor else if r=34 then last else if r=17 then code
  else if r=32 then weights else []

abbrev readCompleteInput : Routine 46 := sequence (ofProgram (unframeProgram 45 0 40 47))
  (sequence (ofProgram (unframeProgram 45 0 34 47))
    (sequence (ofProgram (unframeProgram 45 0 17 47)) (move 45 0 32 47)))

theorem completeInputWord_length (vista : Executable.Vista) (weights : Array Nat) (anchor last : Nat) :
    (completeInputWord vista weights anchor last).length=
      2*anchor.size+1+(2*last.size+1)+(2*(Encoding.vista.encode vista).length+1)+
        ((Encoding.array Encoding.natural).encode weights).length := by
  simp [completeInputWord,List.length_append,Encoding.natural_length,Encoding.frame_length,Nat.add_assoc]

/-- Parse only binary labels and canonical frames. All input copying and
consumption is charged, with no external unary population or round budget. -/
theorem readCompleteInput_executes (vista : Executable.Vista) (weights : Array Nat) (anchor last : Nat) :
    ∃ time ≤ 100*((completeInputWord vista weights anchor last).length+1)^2,
      Executes readCompleteInput (inputStore 46 (completeInputWord vista weights anchor last)) time
        (completeInputFile [] anchor.bits last.bits (Encoding.vista.encode vista)
          ((Encoding.array Encoding.natural).encode weights)) := by
  let code:=Encoding.vista.encode vista
  let values:=(Encoding.array Encoding.natural).encode weights
  let initial:=completeInputFile (completeInputWord vista weights anchor last) [] [] [] []
  let first:=completeInputFile (Encoding.natural.encode last++Encoding.frame code++values) anchor.bits [] [] []
  have a:=unframe_canonical_executes 45 (0:Fin 48) 40 47 (by decide) (by decide) (by decide)
    initial anchor.bits (Encoding.natural.encode last++Encoding.frame code++values)
    (by simp [initial,completeInputFile,completeInputWord,Encoding.natural,List.append_assoc,code,values]) rfl
  have firstStore : Function.update (Function.update initial 0
      (Encoding.natural.encode last++Encoding.frame code++values)) 40 (anchor.bits++initial 40)=first := by
    funext r;fin_cases r <;> simp [initial,first,completeInputFile]
  rw [firstStore] at a
  let second:=completeInputFile (Encoding.frame code++values) anchor.bits last.bits [] []
  have b:=unframe_canonical_executes 45 (0:Fin 48) 34 47 (by decide) (by decide) (by decide)
    first last.bits (Encoding.frame code++values)
    (by simp [first,completeInputFile,Encoding.natural,List.append_assoc]) rfl
  have secondStore : Function.update (Function.update first 0 (Encoding.frame code++values)) 34
      (last.bits++first 34)=second := by
    funext r;fin_cases r <;> simp [first,second,completeInputFile]
  rw [secondStore] at b
  let third:=completeInputFile values anchor.bits last.bits code []
  have c:=unframe_canonical_executes 45 (0:Fin 48) 17 47 (by decide) (by decide) (by decide)
    second code values rfl rfl
  have thirdStore : Function.update (Function.update second 0 values) 17 (code++second 17)=third := by
    funext r;fin_cases r <;> simp [second,third,completeInputFile]
  rw [thirdStore] at c
  have d:=move_executes 45 (0:Fin 48) 32 47 (by decide) (by decide) (by decide) third rfl
  have finalStore : Function.update (Function.update third 32 (third 0++third 32)) 0 []=
      completeInputFile [] anchor.bits last.bits code values := by
    funext r;fin_cases r <;> simp [third,completeInputFile]
  rw [finalStore] at d
  change Executes _ third (6*values.length+4) _ at d
  have initialStore : initial=inputStore 46 (completeInputWord vista weights anchor last) := by
    funext r;fin_cases r <;> simp [initial,completeInputFile,inputStore]
  rw [initialStore] at a
  refine ⟨_,?_,a.sequence (b.sequence (c.sequence d))⟩
  simp only [Encoding.bits_length]
  have length:=completeInputWord_length vista weights anchor last
  have linear : (completeInputWord vista weights anchor last).length+1≤
      ((completeInputWord vista weights anchor last).length+1)^2:=Nat.le_self_pow (by decide) _
  dsimp only [code,values] at *
  omega

end Counting.StackMachine.AuditDescendant
