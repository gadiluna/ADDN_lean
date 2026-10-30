import Counting.StackRowDotLoop
import Counting.StackRowAddHeader

namespace Counting.StackMachine.RowDot
open Routine RowAdd GaussianBits

abbrev initializeAccumulator : Routine 34 := prepend 2 (Encoding.rational.encode 0)
abbrev finish : Routine 34 := sequence (clear 6) (clear 32)
abbrev dotRoutine : Routine 34 := sequence readHeaders
  (sequence initializeAccumulator (sequence loop finish))

theorem initializeAccumulator_executes (left right counter header status : List Bool) :
    Executes initializeAccumulator (file left right [] counter [] [] [] [] header status []) 10
      (file left right (Encoding.rational.encode 0) counter [] [] [] [] header status []) := by
  have ran := prepend_executes (registers:=34) 2 (Encoding.rational.encode 0)
    (file left right [] counter [] [] [] [] header status [])
  have changed : Function.update (file left right [] counter [] [] [] [] header status []) 2
      (Encoding.rational.encode 0++[]) =
      file left right (Encoding.rational.encode 0) counter [] [] [] [] header status [] := by
    funext r; fin_cases r <;> simp [file]
  change Executes initializeAccumulator _ (2*(Encoding.rational.encode 0).length)
    (Function.update (file left right [] counter [] [] [] [] header status []) 2 (Encoding.rational.encode 0++[])) at ran
  rw [changed] at ran
  exact ran

theorem finish_executes (left right accumulator header status : List Bool) :
    Executes finish (file left right accumulator [] [] [] [] [] header status [])
      (header.length+status.length+3) (file left right accumulator [] [] [] [] [] [] [] []) := by
  have first := clear_executes (registers:=34) 6 (file left right accumulator [] [] [] [] [] header status [])
  have firstStore : Function.update (file left right accumulator [] [] [] [] [] header status []) 6 [] =
      file left right accumulator [] [] [] [] [] [] status [] := by
    funext r; fin_cases r <;> simp [file]
  change Executes (clear 6) _ (header.length+1)
    (Function.update (file left right accumulator [] [] [] [] [] header status []) 6 []) at first
  rw [firstStore] at first
  have second := clear_executes (registers:=34) 32 (file left right accumulator [] [] [] [] [] [] status [])
  have secondStore : Function.update (file left right accumulator [] [] [] [] [] [] status []) 32 [] =
      file left right accumulator [] [] [] [] [] [] [] [] := by
    funext r; fin_cases r <;> simp [file]
  change Executes (clear 32) _ (status.length+1)
    (Function.update (file left right accumulator [] [] [] [] [] [] status []) 32 []) at second
  rw [secondStore] at second
  convert first.sequence second using 1
  omega

/-- Canonical equal-length rows are read from their actual binary headers.
Only the supplied suffixes survive besides the canonical scalar result. -/
theorem dot_executes (pairs : List (Rat×Rat)) (leftSuffix rightSuffix : List Bool) :
    ∃ time ≤ 1800*((Encoding.rationalRow.encode (pairs.map Prod.fst)++leftSuffix).length+1)^3+
      6*pairs.length.bits.length+pairs.length*(stepBudget (dotEnvelope pairs 0)+2)+
      (Encoding.natural.encode pairs.length).length+30,
      Executes dotRoutine
        (file (Encoding.rationalRow.encode (pairs.map Prod.fst)++leftSuffix)
          (Encoding.rationalRow.encode (pairs.map Prod.snd)++rightSuffix) [] [] [] [] [] [] [] [] []) time
        (file leftSuffix rightSuffix (Encoding.rational.encode ((pairs.map (fun pair => pair.1*pair.2)).sum))
          [] [] [] [] [] [] [] []) := by
  obtain ⟨headerTime,headerBound,headers⟩ := readHeaders_executes pairs leftSuffix rightSuffix
  have initialized := initializeAccumulator_executes
    (Encoding.sequence (Encoding.framed Encoding.rational) (pairs.map Prod.fst)++leftSuffix)
    (Encoding.sequence (Encoding.framed Encoding.rational) (pairs.map Prod.snd)++rightSuffix)
    (List.replicate pairs.length true) (Encoding.natural.encode pairs.length) [true]
  obtain ⟨loopTime,loopBound,looped⟩ := loop_executes pairs 0 leftSuffix rightSuffix
    (Encoding.natural.encode pairs.length) [true] (dotEnvelope pairs 0) (by rfl)
  rw [dotAcc_eq_sum,zero_add] at looped
  have finished := finish_executes leftSuffix rightSuffix
    (Encoding.rational.encode ((pairs.map (fun pair => pair.1*pair.2)).sum))
    (Encoding.natural.encode pairs.length) [true]
  refine ⟨_,?_,headers.sequence (initialized.sequence (looped.sequence finished))⟩
  simp only [List.length_cons,List.length_nil] at *
  omega

end Counting.StackMachine.RowDot
