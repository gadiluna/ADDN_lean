import Counting.StackPositiveNaturalsLoop

namespace Counting.StackMachine.PositiveNaturals
open Routine

abbrev assemble : Routine 30 := sequence (ofProgram (ListPrograms.reverseProgram 30 2 5))
  (sequence (move 29 6 5 7) (move 29 5 2 7))
abbrev reject : Routine 30 := sequence (clear 2) (pushBit 2 false)
abbrev selectResult : Routine 30 := EncodingPrograms.branchRoutine 28 (pushBit 2 true) reject
abbrev finish : Routine 30 := sequence assemble selectResult

def encodedResult (accepted : Bool) (data : List Bool) : List Bool := if accepted then true::data else [false]

theorem assemble_executes (suffix coefficients header status : List Bool) :
    Executes assemble (RowScale.file [] suffix coefficients.reverse [] [] [] header status [])
      (8*coefficients.length+12*header.length+11)
      (RowScale.file [] suffix (header++coefficients) [] [] [] [] status []) := by
  have reversed := reverse_executes 30 2 5 (by decide) (RowScale.file [] suffix coefficients.reverse [] [] [] header status [])
  have reversedStore : Function.update (Function.update (RowScale.file [] suffix coefficients.reverse [] [] [] header status []) 2 [])
      5 (coefficients.reverse.reverse++[]) = RowScale.file [] suffix [] [] [] coefficients header status [] := by
    funext r; fin_cases r <;> simp [RowScale.file]
  change Executes _ _ (2*coefficients.reverse.length+1)
    (Function.update (Function.update (RowScale.file [] suffix coefficients.reverse [] [] [] header status []) 2 [])
      5 (coefficients.reverse.reverse++[])) at reversed
  rw [List.length_reverse,reversedStore] at reversed
  have prepended := move_executes 29 6 5 7 (by decide) (by decide) (by decide)
    (RowScale.file [] suffix [] [] [] coefficients header status []) rfl
  have prependedStore : Function.update (Function.update (RowScale.file [] suffix [] [] [] coefficients header status []) 5
      (header++coefficients)) 6 [] = RowScale.file [] suffix [] [] [] (header++coefficients) [] status [] := by
    funext r; fin_cases r <;> simp [RowScale.file]
  change Executes _ _ (6*header.length+4)
    (Function.update (Function.update (RowScale.file [] suffix [] [] [] coefficients header status []) 5 (header++coefficients)) 6 []) at prepended
  rw [prependedStore] at prepended
  have moved := move_executes 29 5 2 7 (by decide) (by decide) (by decide)
    (RowScale.file [] suffix [] [] [] (header++coefficients) [] status []) rfl
  have movedStore : Function.update (Function.update (RowScale.file [] suffix [] [] [] (header++coefficients) [] status []) 2
      ((header++coefficients)++[])) 5 [] = RowScale.file [] suffix (header++coefficients) [] [] [] [] status [] := by
    funext r; fin_cases r <;> simp [RowScale.file]
  change Executes _ _ (6*(header++coefficients).length+4)
    (Function.update (Function.update (RowScale.file [] suffix [] [] [] (header++coefficients) [] status []) 2
      ((header++coefficients)++[])) 5 []) at moved
  rw [movedStore] at moved
  convert reversed.sequence (prepended.sequence moved) using 1
  simp only [List.length_append]
  omega

theorem selectResult_executes (suffix data : List Bool) (accepted : Bool) :
    Executes selectResult (RowScale.file [] suffix data [] [] [] [] [accepted] [])
      (1+(if accepted then 1 else data.length+3))
      (RowScale.file [] suffix (encodedResult accepted data) [] [] [] [] [] []) := by
  have reset : Function.update (RowScale.file [] suffix data [] [] [] [] [accepted] []) 28 [] =
      RowScale.file [] suffix data [] [] [] [] [] [] := by
    funext r; fin_cases r <;> simp [RowScale.file]
  apply Signed.branch_bit 28 (pushBit 2 true) reject _ _ accepted _ rfl
  rw [reset]
  cases accepted
  · have cleared := clear_executes (registers := 30) 2 (RowScale.file [] suffix data [] [] [] [] [] [])
    have clearStore : Function.update (RowScale.file [] suffix data [] [] [] [] [] []) 2 [] =
        RowScale.file [] suffix [] [] [] [] [] [] [] := by
      funext r; fin_cases r <;> simp [RowScale.file]
    change Executes (clear 2) _ (data.length+1)
      (Function.update (RowScale.file [] suffix data [] [] [] [] [] []) 2 []) at cleared
    rw [clearStore] at cleared
    have pushed := pushBit_executes (registers := 30) 2 false (RowScale.file [] suffix [] [] [] [] [] [] [])
    have pushStore : Function.update (RowScale.file [] suffix [] [] [] [] [] [] []) 2 [false] =
        RowScale.file [] suffix [false] [] [] [] [] [] [] := by
      funext r; fin_cases r <;> simp [RowScale.file]
    change Executes (pushBit 2 false) _ 1
      (Function.update (RowScale.file [] suffix [] [] [] [] [] [] []) 2 [false]) at pushed
    rw [pushStore] at pushed
    simpa [encodedResult,reject,Nat.add_assoc] using cleared.sequence pushed
  · have pushed := pushBit_executes (registers := 30) 2 true (RowScale.file [] suffix data [] [] [] [] [] [])
    have pushStore : Function.update (RowScale.file [] suffix data [] [] [] [] [] []) 2 (true::data) =
        RowScale.file [] suffix (true::data) [] [] [] [] [] [] := by
      funext r; fin_cases r <;> simp [RowScale.file]
    change Executes (pushBit 2 true) _ 1
      (Function.update (RowScale.file [] suffix data [] [] [] [] [] []) 2 (true::data)) at pushed
    rw [pushStore] at pushed
    exact pushed

theorem finish_executes (suffix coefficients header : List Bool) (accepted : Bool) :
    ∃ time ≤ 9*coefficients.length+13*header.length+16,
      Executes finish (RowScale.file [] suffix coefficients.reverse [] [] [] header [accepted] []) time
        (RowScale.file [] suffix (encodedResult accepted (header++coefficients)) [] [] [] [] [] []) := by
  have assembled := assemble_executes suffix coefficients header [accepted]
  have selected := selectResult_executes suffix (header++coefficients) accepted
  refine ⟨_,?_,assembled.sequence selected⟩
  simp only [List.length_append]
  cases accepted <;> simp <;> omega

end Counting.StackMachine.PositiveNaturals
