import Counting.StackUnframeCanonical
import Counting.StackRoutineMove
import Counting.StackRoutineClean
import Counting.EncodingDag

namespace Counting.StackMachine.AuditPrefix
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

def inputWord (vista : Executable.Vista) (leaders candidate last : Nat) : List Bool :=
  Encoding.natural.encode leaders++Encoding.natural.encode candidate++
    Encoding.natural.encode last++Encoding.vista.encode vista

def inputFile (source leaders candidate last code : List Bool) : Store 50 :=
  fun r=>if r=0 then source else if r=37 then leaders else if r=38 then candidate
    else if r=39 then last else if r=40 then code else []

abbrev readInput : Routine 50 := sequence (ofProgram (unframeProgram 49 0 37 51))
  (sequence (ofProgram (unframeProgram 49 0 38 51))
    (sequence (ofProgram (unframeProgram 49 0 39 51)) (move 49 0 40 51)))

theorem inputWord_length (vista : Executable.Vista) (leaders candidate last : Nat) :
    (inputWord vista leaders candidate last).length=
      2*leaders.size+1+(2*candidate.size+1)+(2*last.size+1)+(Encoding.vista.encode vista).length := by
  simp [inputWord,Encoding.natural_length,List.length_append,Nat.add_assoc]

/-- The three numerical parameters are unframed as binary payloads and
the actual vista word is retained for validation and subsequent scans. -/
theorem readInput_executes (vista : Executable.Vista) (leaders candidate last : Nat) :
    ∃ time ≤ 100*((inputWord vista leaders candidate last).length+1)^2,
      Executes readInput (inputStore 50 (inputWord vista leaders candidate last)) time
        (inputFile [] leaders.bits candidate.bits last.bits (Encoding.vista.encode vista)) := by
  let code:=Encoding.vista.encode vista
  let initial:=inputFile (inputWord vista leaders candidate last) [] [] [] []
  let first:=inputFile (Encoding.natural.encode candidate++Encoding.natural.encode last++code)
    leaders.bits [] [] []
  have a:=unframe_canonical_executes 49 (0:Fin 52) 37 51 (by decide) (by decide) (by decide)
    initial leaders.bits (Encoding.natural.encode candidate++Encoding.natural.encode last++code)
    (by simp [initial,inputFile,inputWord,Encoding.natural,List.append_assoc,code]) rfl
  have firstStore : Function.update (Function.update initial 0
      (Encoding.natural.encode candidate++Encoding.natural.encode last++code)) 37
        (leaders.bits++initial 37)=first := by
    funext r;fin_cases r <;> simp [initial,first,inputFile]
  rw [firstStore] at a
  let second:=inputFile (Encoding.natural.encode last++code) leaders.bits candidate.bits [] []
  have b:=unframe_canonical_executes 49 (0:Fin 52) 38 51 (by decide) (by decide) (by decide)
    first candidate.bits (Encoding.natural.encode last++code)
    (by simp [first,inputFile,Encoding.natural,List.append_assoc]) rfl
  have secondStore : Function.update (Function.update first 0 (Encoding.natural.encode last++code)) 38
      (candidate.bits++first 38)=second := by
    funext r;fin_cases r <;> simp [first,second,inputFile]
  rw [secondStore] at b
  let third:=inputFile code leaders.bits candidate.bits last.bits []
  have c:=unframe_canonical_executes 49 (0:Fin 52) 39 51 (by decide) (by decide) (by decide)
    second last.bits code rfl rfl
  have thirdStore : Function.update (Function.update second 0 code) 39 (last.bits++second 39)=third := by
    funext r;fin_cases r <;> simp [second,third,inputFile]
  rw [thirdStore] at c
  have d:=move_executes 49 (0:Fin 52) 40 51 (by decide) (by decide) (by decide) third rfl
  have finalStore : Function.update (Function.update third 40 (third 0++third 40)) 0 []=
      inputFile [] leaders.bits candidate.bits last.bits code := by
    funext r;fin_cases r <;> simp [third,inputFile]
  rw [finalStore] at d
  change Executes _ third (6*code.length+4) _ at d
  have initialStore : initial=inputStore 50 (inputWord vista leaders candidate last) := by
    funext r;fin_cases r <;> simp [initial,inputFile,inputStore]
  rw [initialStore] at a
  refine ⟨_,?_,a.sequence (b.sequence (c.sequence d))⟩
  simp only [Encoding.bits_length]
  have length:=inputWord_length vista leaders candidate last
  have linear : (inputWord vista leaders candidate last).length+1 ≤
      ((inputWord vista leaders candidate last).length+1)^2 := Nat.le_self_pow (by decide) _
  dsimp only [code] at *
  omega

end Counting.StackMachine.AuditPrefix
