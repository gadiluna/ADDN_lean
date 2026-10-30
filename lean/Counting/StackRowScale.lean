import Counting.StackRowScaleHeader

namespace Counting.StackMachine.RowScale
open Routine

abbrev finish : Routine 30 := sequence (ofProgram (ListPrograms.reverseProgram 30 2 5))
  (sequence (move 29 6 5 7) (sequence (move 29 5 2 7) (clear 28)))
abbrev scaleRoutine : Routine 30 := sequence readHeader (sequence loop finish)

theorem finish_executes (factor suffix coefficients header : List Bool) :
    Executes finish (file factor suffix coefficients.reverse [] [] [] header [true] [])
      (8*coefficients.length+12*header.length+14)
      (file factor suffix (header++coefficients) [] [] [] [] [] []) := by
  have reversed := reverse_executes 30 2 5 (by decide)
    (file factor suffix coefficients.reverse [] [] [] header [true] [])
  have reversedStore : Function.update (Function.update (file factor suffix coefficients.reverse [] [] [] header [true] []) 2 [])
      5 (coefficients.reverse.reverse++[]) = file factor suffix [] [] [] coefficients header [true] [] := by
    funext r; fin_cases r <;> simp [file]
  change Executes _ _ (2*coefficients.reverse.length+1)
    (Function.update (Function.update (file factor suffix coefficients.reverse [] [] [] header [true] []) 2 [])
      5 (coefficients.reverse.reverse++[])) at reversed
  rw [List.length_reverse,reversedStore] at reversed
  have prepended := move_executes 29 6 5 7 (by decide) (by decide) (by decide)
    (file factor suffix [] [] [] coefficients header [true] []) rfl
  have prependedStore : Function.update (Function.update (file factor suffix [] [] [] coefficients header [true] []) 5
      (header++coefficients)) 6 [] = file factor suffix [] [] [] (header++coefficients) [] [true] [] := by
    funext r; fin_cases r <;> simp [file]
  change Executes _ _ (6*header.length+4)
    (Function.update (Function.update (file factor suffix [] [] [] coefficients header [true] []) 5
      (header++coefficients)) 6 []) at prepended
  rw [prependedStore] at prepended
  have moved := move_executes 29 5 2 7 (by decide) (by decide) (by decide)
    (file factor suffix [] [] [] (header++coefficients) [] [true] []) rfl
  have movedStore : Function.update (Function.update (file factor suffix [] [] [] (header++coefficients) [] [true] []) 2
      ((header++coefficients)++[])) 5 [] = file factor suffix (header++coefficients) [] [] [] [] [true] [] := by
    funext r; fin_cases r <;> simp [file]
  change Executes _ _ (6*(header++coefficients).length+4)
    (Function.update (Function.update (file factor suffix [] [] [] (header++coefficients) [] [true] []) 2
      ((header++coefficients)++[])) 5 []) at moved
  rw [movedStore] at moved
  have cleared := clear_executes (registers := 30) 28 (file factor suffix (header++coefficients) [] [] [] [] [true] [])
  have clearedStore : Function.update (file factor suffix (header++coefficients) [] [] [] [] [true] []) 28 [] =
      file factor suffix (header++coefficients) [] [] [] [] [] [] := by
    funext r; fin_cases r <;> simp [file]
  change Executes (clear 28) _ 2 (Function.update (file factor suffix (header++coefficients) [] [] [] [] [true] []) 28 []) at cleared
  rw [clearedStore] at cleared
  convert reversed.sequence (prepended.sequence (moved.sequence cleared)) using 1
  simp only [List.length_append]
  omega

/-- A real finite loop reads the explicit row header, invokes the proved
multiplication program for every coefficient, and emits the canonical row.
The scalar and the input suffix survive; all private registers are empty. -/
theorem scale_executes (factor : Rat) (row : List Rat) (suffix : List Bool)
    (limit : Nat) (bounded : ∀ value∈row,(Encoding.rational.encode value).length≤limit) :
    ∃ time ≤ 1800*((Encoding.rationalRow.encode row++suffix).length+1)^3+
      row.length*(150000000*((Encoding.rational.encode factor).length+limit+1)^3+2)+
      8*(Encoding.sequence (Encoding.framed Encoding.rational) (row.map (factor*·))).length+
      12*(Encoding.natural.encode row.length).length+17,
      Executes scaleRoutine (file (Encoding.rational.encode factor) (Encoding.rationalRow.encode row++suffix) [] [] [] [] [] [] []) time
        (file (Encoding.rational.encode factor) suffix (Encoding.rationalRow.encode (row.map (factor*·))) [] [] [] [] [] []) := by
  obtain ⟨headerTime,headerBound,headerRun⟩ := readHeader_executes (Encoding.rational.encode factor) row suffix
  obtain ⟨loopTime,loopBound,loopRun⟩ := loop_executes factor row suffix [] (Encoding.natural.encode row.length) [true] limit bounded
  simp only [List.append_nil] at loopRun
  have finalRun := finish_executes (Encoding.rational.encode factor) suffix
    (Encoding.sequence (Encoding.framed Encoding.rational) (row.map (factor*·))) (Encoding.natural.encode row.length)
  have result : Encoding.natural.encode row.length++Encoding.sequence (Encoding.framed Encoding.rational) (row.map (factor*·)) =
      Encoding.rationalRow.encode (row.map (factor*·)) := by
    simp only [Encoding.rationalRow,Encoding.list,List.length_map]
  rw [result] at finalRun
  exact ⟨_,by omega,headerRun.sequence (loopRun.sequence finalRun)⟩

end Counting.StackMachine.RowScale
