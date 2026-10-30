import Counting.StackAuditPostSolverBank
import Counting.StackEncodingFrameStore

namespace Counting.StackMachine.AuditPostSolver
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

def metadata (anchor : Nat) (vista : Executable.Vista) : Fin 6 → List Bool :=
  ![[],anchor.bits,Encoding.vista.encode vista,[],[],[]]

def inputWord (vista : Executable.Vista) (candidate anchor : Nat) (values : Option (Array Rat)) : List Bool :=
  Encoding.natural.encode candidate++Encoding.natural.encode anchor++
    Encoding.frame (Encoding.vista.encode vista)++AuditPositive.inputWord values

abbrev prepareInput : Routine 54 := sequence (ofProgram (unframeProgram 53 0 50 55))
  (sequence (ofProgram (unframeProgram 53 0 51 55))
    (sequence (ofProgram (unframeProgram 53 0 52 55)) (frameRoutine 53 50 0 55)))

/-- Parse the real input and rebuild the exact candidate-check input.
The binary anchor and complete vista are retained in external registers. -/
theorem prepareInput_executes (vista : Executable.Vista) (candidate anchor : Nat) (values : Option (Array Rat)) :
    ∃ time ≤ 100*((inputWord vista candidate anchor values).length+1)^2,
      Executes prepareInput (inputStore 54 (inputWord vista candidate anchor values)) time
        (file (AuditCandidate.inputWord values candidate) [] (metadata anchor vista)) := by
  let raw:=AuditPositive.inputWord values
  let code:=Encoding.vista.encode vista
  let initial:=file (inputWord vista candidate anchor values) [] ![[],[],[],[],[],[]]
  let first:=file (Encoding.natural.encode anchor++Encoding.frame code++raw) []
    ![candidate.bits,[],[],[],[],[]]
  have a:=unframe_canonical_executes 53 (0:Fin 56) 50 55 (by decide) (by decide) (by decide)
    initial candidate.bits (Encoding.natural.encode anchor++Encoding.frame code++raw)
    (by simp [initial,file,inputWord,Encoding.natural,List.append_assoc,raw,code]) rfl
  have aResult : Function.update (Function.update initial 0 (Encoding.natural.encode anchor++Encoding.frame code++raw)) 50
      (candidate.bits++initial 50)=first := by
    funext r;fin_cases r <;> simp [initial,first,file]
  rw [aResult] at a
  let second:=file (Encoding.frame code++raw) [] ![candidate.bits,anchor.bits,[],[],[],[]]
  have b:=unframe_canonical_executes 53 (0:Fin 56) 51 55 (by decide) (by decide) (by decide)
    first anchor.bits (Encoding.frame code++raw) (by simp [first,file,Encoding.natural,List.append_assoc]) rfl
  have bResult : Function.update (Function.update first 0 (Encoding.frame code++raw)) 51 (anchor.bits++first 51)=second := by
    funext r;fin_cases r <;> simp [first,second,file]
  rw [bResult] at b
  let third:=file raw [] ![candidate.bits,anchor.bits,code,[],[],[]]
  have c:=unframe_canonical_executes 53 (0:Fin 56) 52 55 (by decide) (by decide) (by decide)
    second code raw rfl rfl
  have cResult : Function.update (Function.update second 0 raw) 52 (code++second 52)=third := by
    funext r;fin_cases r <;> simp [second,third,file]
  rw [cResult] at c
  have d:=frame_executes_updates 53 (50:Fin 56) 0 55 (by decide) (by decide) (by decide) third rfl
  have dResult : Function.update (Function.update third 50 []) 0 (Encoding.frame (third 50)++third 0)=
      file (AuditCandidate.inputWord values candidate) [] (metadata anchor vista) := by
    funext r;fin_cases r <;> simp [third,file,metadata,AuditCandidate.inputWord,Encoding.natural,raw,code]
  rw [dResult] at d
  change Executes _ third (5*candidate.bits.length+4) _ at d
  have start : initial=inputStore 54 (inputWord vista candidate anchor values) := by
    funext r;fin_cases r <;> simp [initial,file,inputStore]
  rw [start] at a
  have inputSize : (inputWord vista candidate anchor values).length=
      2*candidate.size+1+(2*anchor.size+1)+(2*code.length+1)+raw.length := by
    simp only [inputWord,List.length_append,Encoding.natural_length,Encoding.frame_length,code,raw]
  have linear : (inputWord vista candidate anchor values).length+1 ≤
      ((inputWord vista candidate anchor values).length+1)^2 := Nat.le_self_pow (by decide) _
  refine ⟨_,?_,a.sequence (b.sequence (c.sequence d))⟩
  simp only [Encoding.bits_length]
  omega

end Counting.StackMachine.AuditPostSolver
