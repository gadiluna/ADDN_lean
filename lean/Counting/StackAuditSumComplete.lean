import Counting.StackAuditSumSpec
import Counting.StackRoutineClean
import Counting.StackRoutineMove

namespace Counting.StackMachine.AuditSum
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

def inputWord (values : List Nat) (candidate : Nat) : List Bool :=
  Encoding.natural.encode candidate++(Encoding.list Encoding.natural).encode values

abbrev complete : Routine 22 := sequence (ofProgram (unframeProgram 21 0 21 4))
  (sequence (move 21 0 22 4) (sequence check (sequence (clear 21) (clear 22))))

theorem complete_executes (values : List Nat) (candidate : Nat) :
    ∃ time ≤ 4000*((inputWord values candidate).length+1)^3,
      Executes complete (inputStore 22 (inputWord values candidate)) time
        (outputStore 22 [accepts values candidate]) := by
  let word := (Encoding.list Encoding.natural).encode values
  let start := file [] [] [] (inputWord values candidate) [] []
  have a := unframe_canonical_executes 21 (0:Fin 24) 21 4 (by decide) (by decide) (by decide)
    start candidate.bits word rfl rfl
  let parsed := file [] candidate.bits [] word [] []
  have as' : Function.update (Function.update start 0 word) 21 (candidate.bits++start 21)=parsed := by
    funext r;fin_cases r <;> simp [start,parsed,file]
  rw [as'] at a
  have b := move_executes 21 (0:Fin 24) 22 4 (by decide) (by decide) (by decide) parsed rfl
  let ready := file [] candidate.bits word [] [] []
  have bs : Function.update (Function.update parsed 22 (parsed 0++parsed 22)) 0 []=ready := by
    funext r;fin_cases r <;> simp [parsed,ready,file]
  rw [bs] at b
  change Executes _ _ (6*word.length+4) _ at b
  obtain ⟨checkTime,checkBound,c⟩ := check_executes values candidate
  let checked := file [] candidate.bits word [] [] [accepts values candidate]
  have d := clear_executes (21:Fin 24) checked
  let noCandidate := file [] [] word [] [] [accepts values candidate]
  have ds : Function.update checked 21 []=noCandidate := by
    funext r;fin_cases r <;> simp [checked,noCandidate,file]
  rw [ds] at d
  change Executes _ _ (candidate.bits.length+1) _ at d
  have e := clear_executes (22:Fin 24) noCandidate
  have es : Function.update noCandidate 22 []=outputStore 22 [accepts values candidate] := by
    funext r;fin_cases r <;> simp [noCandidate,file,outputStore]
  rw [es] at e
  change Executes _ _ (word.length+1) _ at e
  have result := a.sequence (b.sequence (c.sequence (d.sequence e)))
  have first : start=inputStore 22 (inputWord values candidate) := by
    funext r;fin_cases r <;> simp [start,file,inputStore]
  rw [first] at result
  refine ⟨_,?_,result⟩
  have inputLength : (inputWord values candidate).length=2*candidate.size+1+word.length := by
    simp only [inputWord,List.length_append,Encoding.natural_length,word]
  let size := (inputWord values candidate).length+1
  have base : word.length+candidate.size+1 ≤ size := by dsimp only [size];omega
  have checkLimit := checkBound.trans (Nat.mul_le_mul_left 3000 (Nat.pow_le_pow_left base 3))
  have linear : size ≤ size^3 := Nat.le_self_pow (by decide) _
  have one : 1 ≤ size^3 := Nat.one_le_pow _ _ (by dsimp only [size];omega)
  have wordSize : word.length ≤ size := by dsimp only [size];omega
  have candidateSize : candidate.size ≤ size := by dsimp only [size];omega
  simp only [Encoding.bits_length]
  change _ ≤ 4000*size^3
  omega

theorem complete_halts (values : List Nat) (candidate : Nat) :
    ∃ time last,time ≤ 4000*((inputWord values candidate).length+1)^3 ∧
      HaltsAt complete.program (inputWord values candidate) time last ∧
      last.store 1=[accepts values candidate] := by
  obtain ⟨time,bounded,last,ran,halted,stored⟩ := complete_executes values candidate
  exact ⟨time,last,bounded,⟨ran,halted⟩,by rw [stored];rfl⟩

end Counting.StackMachine.AuditSum
