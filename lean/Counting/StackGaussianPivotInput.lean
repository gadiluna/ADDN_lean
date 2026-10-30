import Counting.StackGaussianPivotHeader
import Counting.StackLookupDrop
import Counting.StackUnframeCanonical

namespace Counting.StackMachine.GaussianPivot
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

abbrev copyColumn : Routine 29 := ofProgram (ListPrograms.copyProgram 28 1 2 4)
abbrev copySkip : Routine 29 := ofProgram (ListPrograms.copyProgram 28 1 3 4)
abbrev subtractCount : Routine 29 := ofProgram (Lookup.dropProgram 29 29 3)
abbrev prepareCounters : Routine 29 := sequence copyColumn (sequence copySkip (sequence subtractCount
  (sequence (pushBit 1 true) (sequence (pushBit 2 true) (pushBit 30 true)))))

theorem prepareCounters_executes (matrix : List Bool) (count pivot : Nat) :
    Executes prepareCounters (seed matrix (List.replicate pivot true) (List.replicate count true))
      (12*pivot+13) (state matrix pivot pivot (List.replicate (count-pivot) true) true) := by
  let p := List.replicate pivot true
  let c := List.replicate count true
  let initial := seed matrix p c
  let first := file matrix p p [] [] [] [] [] c []
  let second := file matrix p p p [] [] [] [] c []
  let third := file matrix p p [] [] [] [] [] (List.replicate (count-pivot) true) []
  let fourth := file matrix (true::p) p [] [] [] [] [] (List.replicate (count-pivot) true) []
  let fifth := file matrix (true::p) (true::p) [] [] [] [] [] (List.replicate (count-pivot) true) []
  have copyFirst := copy_executes 28 (1 : Fin 31) 2 4 (by decide) (by decide) (by decide) initial rfl
  have firstResult : Function.update initial 2 (initial 1++initial 2)=first := by
    funext r;fin_cases r <;> simp [initial,first,file]
  rw [firstResult] at copyFirst
  have copySecond := copy_executes 28 (1 : Fin 31) 3 4 (by decide) (by decide) (by decide) first rfl
  have secondResult : Function.update first 3 (first 1++first 3)=second := by
    funext r;fin_cases r <;> simp [first,second,file]
  rw [secondResult] at copySecond
  have dropped := Lookup.drop_executes 29 (29 : Fin 31) 3 (by decide) second
  have thirdResult : Function.update (Function.update second 3 []) 29 ((second 29).drop (second 3).length)=third := by
    funext r;fin_cases r <;> simp [second,third,file,p,c]
  rw [thirdResult] at dropped
  have pushFirst := pushBit_executes (1 : Fin 31) true third
  have fourthResult : Function.update third 1 (true::third 1)=fourth := by
    funext r;fin_cases r <;> simp [third,fourth,file]
  rw [fourthResult] at pushFirst
  have pushSecond := pushBit_executes (2 : Fin 31) true fourth
  have fifthResult : Function.update fourth 2 (true::fourth 2)=fifth := by
    funext r;fin_cases r <;> simp [fourth,fifth,file]
  rw [fifthResult] at pushSecond
  have pushActive := pushBit_executes (30 : Fin 31) true fifth
  have final : Function.update fifth 30 (true::fifth 30)=state matrix pivot pivot (List.replicate (count-pivot) true) true := by
    funext r;fin_cases r <;> simp [fifth,p,state,file,List.replicate_succ]
  rw [final] at pushActive
  have firstRun : Executes copyColumn initial (5*pivot+2) first := by
    simpa [initial,p,file] using copyFirst
  have secondRun : Executes copySkip first (5*pivot+2) second := by
    simpa [first,p,file] using copySecond
  have dropRun : Executes subtractCount second (2*pivot+1) third := by
    simpa [second,p,file] using dropped
  convert firstRun.sequence (secondRun.sequence (dropRun.sequence (pushFirst.sequence (pushSecond.sequence pushActive)))) using 1
  omega

/-- The only external index is a bounded unary diagonal index; the number
of candidate rows is obtained from the binary matrix header at run time. -/
def inputWord (rows : List (List Rat)) (pivot : Nat) : List Bool :=
  Encoding.frame (List.replicate pivot true)++Encoding.rationalMatrix.encode rows

abbrev prepareInput : Routine 29 := sequence (ofProgram (unframeProgram 28 0 1 5))
  (sequence readCount prepareCounters)

theorem prepareInput_executes (rows : List (List Rat)) (pivot : Nat) :
    ∃ time ≤ 2000*((inputWord rows pivot).length+1)^3,
      Executes prepareInput (seed (inputWord rows pivot) [] []) time
        (state (Encoding.rationalMatrix.encode rows) pivot pivot (List.replicate (rows.length-pivot) true) true) := by
  have parsed := unframe_canonical_executes 28 (0 : Fin 31) 1 5 (by decide) (by decide) (by decide)
    (seed (inputWord rows pivot) [] []) (List.replicate pivot true) (Encoding.rationalMatrix.encode rows) rfl rfl
  have parseResult : Function.update (Function.update (seed (inputWord rows pivot) [] []) 0 (Encoding.rationalMatrix.encode rows))
      1 (List.replicate pivot true++seed (inputWord rows pivot) [] [] 1) = seed (Encoding.rationalMatrix.encode rows) (List.replicate pivot true) [] := by
    funext r;fin_cases r <;> simp [file]
  rw [parseResult] at parsed
  obtain ⟨countTime,countBound,counted⟩ := readCount_executes rows (List.replicate pivot true)
  have counters := prepareCounters_executes (Encoding.rationalMatrix.encode rows) rows.length pivot
  refine ⟨5*pivot+2+1+(countTime+1+(12*pivot+13)),?_,?_⟩
  · have length : (inputWord rows pivot).length=2*pivot+1+(Encoding.rationalMatrix.encode rows).length := by
      simp [inputWord,Encoding.frame_length]
    have power := Nat.pow_le_pow_left
      (show (Encoding.rationalMatrix.encode rows).length+1≤(inputWord rows pivot).length+1 by omega) 3
    have linear := Nat.le_self_pow (by decide : 3≠0) ((inputWord rows pivot).length+1)
    omega
  · simpa only [List.length_replicate] using parsed.sequence (counted.sequence counters)

end Counting.StackMachine.GaussianPivot
