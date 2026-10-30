import Counting.StackRowAddHeader

namespace Counting.StackMachine.RowAdd
open Routine

abbrev finish : Routine 34 := sequence (ofProgram (ListPrograms.reverseProgram 34 2 8))
  (sequence (move 33 6 8 7) (sequence (move 33 8 2 7) (clear 32)))
abbrev addRoutine : Routine 34 := sequence readHeaders (sequence loop finish)

theorem finish_executes (left right coefficients header : List Bool) :
    Executes finish (file left right coefficients.reverse [] [] [] [] [] header [true] [])
      (8*coefficients.length+12*header.length+14)
      (file left right (header++coefficients) [] [] [] [] [] [] [] []) := by
  have reversed := reverse_executes 34 2 8 (by decide)
    (file left right coefficients.reverse [] [] [] [] [] header [true] [])
  have reversedStore : Function.update (Function.update (file left right coefficients.reverse [] [] [] [] [] header [true] []) 2 [])
      8 (coefficients.reverse.reverse++[]) = file left right [] [] [] [] coefficients [] header [true] [] := by
    funext r; fin_cases r <;> simp [file]
  change Executes _ _ (2*coefficients.reverse.length+1)
    (Function.update (Function.update (file left right coefficients.reverse [] [] [] [] [] header [true] []) 2 [])
      8 (coefficients.reverse.reverse++[])) at reversed
  rw [List.length_reverse,reversedStore] at reversed
  have prepended := move_executes 33 6 8 7 (by decide) (by decide) (by decide)
    (file left right [] [] [] [] coefficients [] header [true] []) rfl
  have prependedStore : Function.update (Function.update (file left right [] [] [] [] coefficients [] header [true] []) 8
      (header++coefficients)) 6 [] = file left right [] [] [] [] (header++coefficients) [] [] [true] [] := by
    funext r; fin_cases r <;> simp [file]
  change Executes _ _ (6*header.length+4)
    (Function.update (Function.update (file left right [] [] [] [] coefficients [] header [true] []) 8
      (header++coefficients)) 6 []) at prepended
  rw [prependedStore] at prepended
  have moved := move_executes 33 8 2 7 (by decide) (by decide) (by decide)
    (file left right [] [] [] [] (header++coefficients) [] [] [true] []) rfl
  have movedStore : Function.update (Function.update (file left right [] [] [] [] (header++coefficients) [] [] [true] []) 2
      ((header++coefficients)++[])) 8 [] = file left right (header++coefficients) [] [] [] [] [] [] [true] [] := by
    funext r; fin_cases r <;> simp [file]
  change Executes _ _ (6*(header++coefficients).length+4)
    (Function.update (Function.update (file left right [] [] [] [] (header++coefficients) [] [] [true] []) 2
      ((header++coefficients)++[])) 8 []) at moved
  rw [movedStore] at moved
  have cleared := clear_executes (registers := 34) 32 (file left right (header++coefficients) [] [] [] [] [] [] [true] [])
  have clearedStore : Function.update (file left right (header++coefficients) [] [] [] [] [] [] [true] []) 32 [] =
      file left right (header++coefficients) [] [] [] [] [] [] [] [] := by
    funext r; fin_cases r <;> simp [file]
  change Executes (clear 32) _ 2 (Function.update (file left right (header++coefficients) [] [] [] [] [] [] [true] []) 32 []) at cleared
  rw [clearedStore] at cleared
  convert reversed.sequence (prepended.sequence (moved.sequence cleared)) using 1
  simp only [List.length_append]
  omega

/-- A bounded finite loop reads both coefficient streams and calls the actual
rational adder. The pair list describes equal-length rows; no length agreement
is inferred from untrusted input. Both suffixes survive and all work is erased. -/
theorem add_executes (pairs : List (Rat×Rat)) (leftSuffix rightSuffix : List Bool)
    (limit : Nat) (bounded : ∀ pair∈pairs,
      (Encoding.rational.encode pair.1).length+(Encoding.rational.encode pair.2).length≤limit) :
    ∃ time ≤ 1800*((Encoding.rationalRow.encode (pairs.map Prod.fst)++leftSuffix).length+1)^3+
      6*pairs.length.bits.length+pairs.length*(700000000*(limit+1)^3+2)+
      8*(Encoding.sequence (Encoding.framed Encoding.rational) (pairs.map (fun pair => pair.1+pair.2))).length+
      12*(Encoding.natural.encode pairs.length).length+22,
      Executes addRoutine (file (Encoding.rationalRow.encode (pairs.map Prod.fst)++leftSuffix)
        (Encoding.rationalRow.encode (pairs.map Prod.snd)++rightSuffix) [] [] [] [] [] [] [] [] []) time
        (file leftSuffix rightSuffix (Encoding.rationalRow.encode (pairs.map (fun pair => pair.1+pair.2)))
          [] [] [] [] [] [] [] []) := by
  obtain ⟨headerTime,headerBound,headerRun⟩ := readHeaders_executes pairs leftSuffix rightSuffix
  obtain ⟨loopTime,loopBound,loopRun⟩ := loop_executes pairs leftSuffix rightSuffix [] (Encoding.natural.encode pairs.length) [true] limit bounded
  simp only [List.append_nil] at loopRun
  have finalRun := finish_executes leftSuffix rightSuffix
    (Encoding.sequence (Encoding.framed Encoding.rational) (pairs.map (fun pair => pair.1+pair.2))) (Encoding.natural.encode pairs.length)
  have result : Encoding.natural.encode pairs.length++Encoding.sequence (Encoding.framed Encoding.rational) (pairs.map (fun pair => pair.1+pair.2)) =
      Encoding.rationalRow.encode (pairs.map (fun pair => pair.1+pair.2)) := by
    simp only [Encoding.rationalRow,Encoding.list,List.length_map]
  rw [result] at finalRun
  exact ⟨_,by omega,headerRun.sequence (loopRun.sequence finalRun)⟩

end Counting.StackMachine.RowAdd
