import Counting.StackAuditCandidateBank

namespace Counting.StackMachine.AuditCandidate
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

abbrev keepValues : Routine 34 := sequence (move 33 33 1 35) (pushBit 1 true)
abbrev rejectValues : Routine 34 := sequence (clear 33) (pushBit 1 false)
abbrev returnValues : Routine 34 := branchRoutine 1 keepValues rejectValues
abbrev checkValues : Routine 34 := sequence (move 33 1 33 35) (sequence checkSum returnValues)

private theorem keep_executes (candidate word : List Bool) :
    Executes keepValues (file [] [] candidate word) (6*word.length+6)
      (file [] (true::word) candidate []) := by
  have a := move_executes 33 (33:Fin 36) 1 35 (by decide) (by decide) (by decide) (file [] [] candidate word) rfl
  have as' : Function.update (Function.update (file [] [] candidate word) 1 (word++[])) 33 []=
      file [] word candidate [] := by funext r;fin_cases r <;> simp [file]
  change Executes _ _ (6*word.length+4)
    (Function.update (Function.update (file [] [] candidate word) 1 (word++[])) 33 []) at a
  rw [as'] at a
  have b := pushBit_executes (1:Fin 36) true (file [] word candidate [])
  have bs : Function.update (file [] word candidate []) 1 (true::word)=file [] (true::word) candidate [] := by
    funext r;fin_cases r <;> simp [file]
  change Executes _ _ 1 (Function.update (file [] word candidate []) 1 (true::word)) at b
  rw [bs] at b
  exact a.sequence b

private theorem reject_executes (candidate word : List Bool) :
    Executes rejectValues (file [] [] candidate word) (word.length+3) (file [] [false] candidate []) := by
  have a := clear_executes (33:Fin 36) (file [] [] candidate word)
  have as' : Function.update (file [] [] candidate word) 33 []=file [] [] candidate [] := by
    funext r;fin_cases r <;> simp [file]
  change Executes _ _ (word.length+1) _ at a
  rw [as'] at a
  have b := pushBit_executes (1:Fin 36) false (file [] [] candidate [])
  have bs : Function.update (file [] [] candidate []) 1 [false]=file [] [false] candidate [] := by
    funext r;fin_cases r <;> simp [file]
  change Executes _ _ 1 (Function.update (file [] [] candidate []) 1 [false]) at b
  rw [bs] at b
  exact a.sequence b

theorem returnValues_executes (candidate word : List Bool) (accepted : Bool) :
    ∃ time ≤ 6*word.length+7,
      Executes returnValues (file [] [accepted] candidate word) time
        (file [] (if accepted then true::word else [false]) candidate []) := by
  have popped : Function.update (file [] [accepted] candidate word) 1 []=file [] [] candidate word := by
    funext r;fin_cases r <;> simp [file]
  cases accepted
  · have ran := branch_executes_false (1:Fin 36) keepValues rejectValues
      (file [] [false] candidate word) _ [] (word.length+3) rfl
      (by rw [popped];exact reject_executes candidate word)
    exact ⟨_,by omega,ran⟩
  · have ran := branch_executes_true (1:Fin 36) keepValues rejectValues
      (file [] [true] candidate word) _ [] (6*word.length+6) rfl
      (by rw [popped];exact keep_executes candidate word)
    exact ⟨_,by omega,ran⟩

theorem checkValues_executes (natural : Array Nat) (candidate : Nat) :
    ∃ time ≤ 4000*(((Encoding.array Encoding.natural).encode natural).length+candidate.size+1)^3,
      Executes checkValues (file [] ((Encoding.array Encoding.natural).encode natural) candidate.bits []) time
        (file [] ((Encoding.optional (Encoding.array Encoding.natural)).encode
          (if AuditSum.accepts natural.toList candidate then some natural else none)) candidate.bits []) := by
  let word := (Encoding.array Encoding.natural).encode natural
  have a := move_executes 33 (1:Fin 36) 33 35 (by decide) (by decide) (by decide)
    (file [] word candidate.bits []) rfl
  have as' : Function.update (Function.update (file [] word candidate.bits []) 33 (word++[])) 1 []=
      file [] [] candidate.bits word := by funext r;fin_cases r <;> simp [file]
  change Executes _ _ (6*word.length+4)
    (Function.update (Function.update (file [] word candidate.bits []) 33 (word++[])) 1 []) at a
  rw [as'] at a
  obtain ⟨checkTime,checkBound,b⟩ := checkSum_executes natural candidate
  obtain ⟨returnTime,returnBound,c⟩ := returnValues_executes candidate.bits word (AuditSum.accepts natural.toList candidate)
  have output : (if AuditSum.accepts natural.toList candidate then true::word else [false])=
      (Encoding.optional (Encoding.array Encoding.natural)).encode
        (if AuditSum.accepts natural.toList candidate then some natural else none) := by
    split <;> rfl
  rw [output] at c
  refine ⟨_,?_,a.sequence (b.sequence c)⟩
  let size := word.length+candidate.size+1
  have linear : size ≤ size^3 := Nat.le_self_pow (by decide) _
  have one : 1 ≤ size^3 := Nat.one_le_pow _ _ (by dsimp only [size];omega)
  have wordSize : word.length ≤ size := by dsimp only [size];omega
  change checkTime ≤ 3000*size^3 at checkBound
  change _ ≤ 4000*size^3
  omega

end Counting.StackMachine.AuditCandidate
