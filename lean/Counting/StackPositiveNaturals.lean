import Counting.StackPositiveNaturalsFinish
import Counting.StackRowScaleBounds

namespace Counting.StackMachine.PositiveNaturals
open Routine

abbrev conversion : Routine 30 := sequence RowScale.readHeader (sequence loop finish)

theorem conversion_executes (row : List Rat) (suffix : List Bool)
    (limit : Nat) (bounded : ∀ value∈row,(Encoding.rational.encode value).length≤limit) :
    ∃ time ≤ 1800*((Encoding.rationalRow.encode row++suffix).length+1)^3+
        row.length*(5000*(limit+1)+2)+
        9*(Encoding.sequence Encoding.natural (row.map (fun value => value.num.toNat))).length+
        13*(Encoding.natural.encode row.length).length+19,
      Executes conversion (RowScale.file [] (Encoding.rationalRow.encode row++suffix) [] [] [] [] [] [] []) time
        (RowScale.file [] suffix (Counting.PositiveNaturals.output row) [] [] [] [] [] []) := by
  obtain ⟨headerTime,headerBound,headerRun⟩ := RowScale.readHeader_executes [] row suffix
  obtain ⟨loopTime,loopBound,loopRun⟩ := loop_executes row suffix [] (Encoding.natural.encode row.length) true limit bounded
  simp only [List.append_nil,Bool.true_and] at loopRun
  obtain ⟨finishTime,finishBound,finished⟩ := finish_executes suffix
    (Encoding.sequence Encoding.natural (row.map (fun value => value.num.toNat)))
    (Encoding.natural.encode row.length) (row.all Counting.PositiveNaturals.guard)
  have outputEq : encodedResult (row.all Counting.PositiveNaturals.guard)
      (Encoding.natural.encode row.length++Encoding.sequence Encoding.natural (row.map (fun value => value.num.toNat))) =
      Counting.PositiveNaturals.output row := by
    rw [Counting.PositiveNaturals.output_eq]
    simp only [encodedResult,Encoding.list,List.length_map]
  rw [outputEq] at finished
  exact ⟨_,by omega,headerRun.sequence (loopRun.sequence finished)⟩

theorem output_length_le (row : List Rat) :
    (Counting.PositiveNaturals.output row).length ≤ (Encoding.rationalRow.encode row).length+1 := by
  have fields := Counting.PositiveNaturals.output_sequence_length row
  rw [Counting.PositiveNaturals.output_eq]
  split
  · simp only [List.length_cons,Encoding.list,List.length_map,List.length_append]
    change _ ≤ (Encoding.natural.encode row.length++Encoding.sequence (Encoding.framed Encoding.rational) row).length+1
    rw [List.length_append]
    omega
  · simp

theorem conversion_executes_polynomial (row : List Rat) (suffix : List Bool) :
    ∃ time ≤ 9000*((Encoding.rationalRow.encode row).length+suffix.length+1)^3,
      Executes conversion (RowScale.file [] (Encoding.rationalRow.encode row++suffix) [] [] [] [] [] [] []) time
        (RowScale.file [] suffix (Counting.PositiveNaturals.output row) [] [] [] [] [] []) := by
  let size := (Encoding.rationalRow.encode row).length+suffix.length
  obtain ⟨time,bounded,ran⟩ := conversion_executes row suffix (Encoding.rationalRow.encode row).length
    (RowScale.member_row_length_le row)
  refine ⟨time,?_,ran⟩
  have outputBound := Counting.PositiveNaturals.output_sequence_length row
  have count := RowScale.fields_count_le row
  have rowLength : (Encoding.rationalRow.encode row).length=(Encoding.natural.encode row.length).length+
      (Encoding.sequence (Encoding.framed Encoding.rational) row).length := List.length_append
  have countBound : row.length ≤ size+1 := by omega
  have factorBound : 5000*((Encoding.rationalRow.encode row).length+1)+2 ≤ 5002*(size+1) := by omega
  have loopBound := Nat.mul_le_mul countBound factorBound
  have square : (size+1)^2 ≤ (size+1)^3 := Nat.pow_le_pow_right (by omega) (by decide)
  have linear : size+1 ≤ (size+1)^3 := Nat.le_self_pow (by decide) _
  have positive : 1≤(size+1)^3 := Nat.one_le_pow' 3 size
  simp only [List.length_append] at bounded
  change time ≤ 1800*(size+1)^3+row.length*(5000*((Encoding.rationalRow.encode row).length+1)+2)+
    9*(Encoding.sequence Encoding.natural (row.map (fun value => value.num.toNat))).length+
    13*(Encoding.natural.encode row.length).length+19 at bounded
  have outputSize : (Encoding.sequence Encoding.natural (row.map (fun value => value.num.toNat))).length ≤ size := by omega
  have headerSize : (Encoding.natural.encode row.length).length ≤ size := by omega
  change time ≤ 9000*(size+1)^3
  nlinarith

abbrev complete : Routine 30 := sequence (move 29 0 1 7) (sequence conversion (move 29 2 1 7))

theorem complete_halts (row : List Rat) :
    ∃ steps output, steps ≤ 10000*((Encoding.rationalRow.encode row).length+1)^3 ∧
      HaltsAt complete.program (Encoding.rationalRow.encode row) steps output ∧
      output.store 1=Counting.PositiveNaturals.output row := by
  let input := Encoding.rationalRow.encode row
  let result := Counting.PositiveNaturals.output row
  have movedInput := move_executes 29 0 1 7 (by decide) (by decide) (by decide)
    (RowScale.file input [] [] [] [] [] [] [] []) rfl
  have inputStore : Function.update (Function.update (RowScale.file input [] [] [] [] [] [] [] []) 1 (input++[])) 0 [] =
      RowScale.file [] input [] [] [] [] [] [] [] := by
    funext r; fin_cases r <;> simp [RowScale.file]
  change Executes _ _ (6*input.length+4)
    (Function.update (Function.update (RowScale.file input [] [] [] [] [] [] [] []) 1 (input++[])) 0 []) at movedInput
  rw [inputStore] at movedInput
  obtain ⟨conversionTime,conversionBound,converted⟩ := conversion_executes_polynomial row []
  simp only [List.append_nil,List.length_nil,Nat.add_zero] at conversionBound converted
  have movedOutput := move_executes 29 2 1 7 (by decide) (by decide) (by decide)
    (RowScale.file [] [] result [] [] [] [] [] []) rfl
  have outputStore : Function.update (Function.update (RowScale.file [] [] result [] [] [] [] [] []) 1 (result++[])) 2 [] =
      RowScale.file [] result [] [] [] [] [] [] [] := by
    funext r; fin_cases r <;> simp [RowScale.file]
  change Executes _ _ (6*result.length+4)
    (Function.update (Function.update (RowScale.file [] [] result [] [] [] [] [] []) 1 (result++[])) 2 []) at movedOutput
  rw [outputStore] at movedOutput
  obtain ⟨finish,ran,halted,stored⟩ := movedInput.sequence (converted.sequence movedOutput)
  refine ⟨6*input.length+4+1+(conversionTime+1+(6*result.length+4)),finish,?_,⟨?_,halted⟩,?_⟩
  · have resultBound := output_length_le row
    have linear : input.length+1 ≤ (input.length+1)^3 := Nat.le_self_pow (by decide) _
    change result.length ≤ input.length+1 at resultBound
    change conversionTime ≤ 9000*(input.length+1)^3 at conversionBound
    change _ ≤ 10000*(input.length+1)^3
    omega
  · have start : initial complete.program input=⟨0,RowScale.file input [] [] [] [] [] [] [] []⟩ := by
      apply congrArg (Config.mk _); funext r; fin_cases r <;> rfl
    rw [start]
    exact ran
  · rw [stored]
    rfl

end Counting.StackMachine.PositiveNaturals
