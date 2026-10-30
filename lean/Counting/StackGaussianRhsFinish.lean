import Counting.StackGaussianRhsLoop

namespace Counting.StackMachine.GaussianRhs
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

abbrev readHeader : Routine 11 := sequence (ofProgram (unframeProgram 10 0 12 6)) (frameRoutine 10 12 11 6)
abbrev finish : Routine 11 := sequence (ofProgram (ListPrograms.reverseProgram 11 1 12))
  (sequence (move 10 11 12 6) (move 10 12 1 6))
abbrev extract : Routine 11 := sequence readHeader (sequence loop finish)

theorem readHeader_executes (rows : List (List Rat)) (column : Nat) :
    Executes readHeader (state (Encoding.rationalMatrix.encode rows) [] column (List.replicate rows.length true) [])
      (10*rows.length.bits.length+7)
      (state (Encoding.sequence (Encoding.framed Encoding.rationalRow) rows) [] column
        (List.replicate rows.length true) (Encoding.natural.encode rows.length)) := by
  let source := Encoding.rationalMatrix.encode rows
  let suffix := Encoding.sequence (Encoding.framed Encoding.rationalRow) rows
  let counter := List.replicate rows.length true
  let initial := state source [] column counter []
  let parsed := file suffix [] [] [] (List.replicate (column+1) true) [] counter [] rows.length.bits
  have a := unframe_canonical_executes 10 (0 : Fin 13) 12 6 (by decide) (by decide) (by decide)
    initial rows.length.bits suffix rfl rfl
  have aStore : Function.update (Function.update initial 0 suffix) 12 (rows.length.bits++[]) = parsed := by
    funext r;fin_cases r <;> simp [initial,parsed,state,file]
  change Executes _ initial (5*rows.length.bits.length+2)
    (Function.update (Function.update initial 0 suffix) 12 (rows.length.bits++[])) at a
  rw [aStore] at a
  have b := frame_executes_updates 10 (12 : Fin 13) 11 6 (by decide) (by decide) (by decide) parsed rfl
  have bStore : Function.update (Function.update parsed 12 []) 11 (Encoding.frame rows.length.bits++[])=
      state suffix [] column counter (Encoding.natural.encode rows.length) := by
    funext r;fin_cases r <;> simp [parsed,state,file,Encoding.natural]
  change Executes _ parsed (5*rows.length.bits.length+4)
    (Function.update (Function.update parsed 12 []) 11 (Encoding.frame rows.length.bits++[])) at b
  rw [bStore] at b
  convert a.sequence b using 1
  omega

theorem finish_executes (source output header : List Bool) (column : Nat) :
    Executes finish (state source output.reverse column [] header)
      (8*output.length+12*header.length+11)
      (state source (header++output) column [] []) := by
  let initial := state source output.reverse column [] header
  let reversed := file source [] [] [] (List.replicate (column+1) true) [] [] header output
  let joined := file source [] [] [] (List.replicate (column+1) true) [] [] [] (header++output)
  have a := reverse_executes 11 (1 : Fin 13) 12 (by decide) initial
  have aStore : Function.update (Function.update initial 1 []) 12 (output.reverse.reverse++[])=reversed := by
    funext r;fin_cases r <;> simp [initial,reversed,state,file]
  change Executes _ initial (2*output.reverse.length+1)
    (Function.update (Function.update initial 1 []) 12 (output.reverse.reverse++[])) at a
  rw [aStore,List.length_reverse] at a
  have b := move_executes 10 (11 : Fin 13) 12 6 (by decide) (by decide) (by decide) reversed rfl
  have bStore : Function.update (Function.update reversed 12 (header++output)) 11 []=joined := by
    funext r;fin_cases r <;> simp [reversed,joined,file]
  change Executes _ reversed (6*header.length+4)
    (Function.update (Function.update reversed 12 (header++output)) 11 []) at b
  rw [bStore] at b
  have c := move_executes 10 (12 : Fin 13) 1 6 (by decide) (by decide) (by decide) joined rfl
  have cStore : Function.update (Function.update joined 1 ((header++output)++[])) 12 []=
      state source (header++output) column [] [] := by
    funext r;fin_cases r <;> simp [joined,state,file]
  change Executes _ joined (6*(header++output).length+4)
    (Function.update (Function.update joined 1 ((header++output)++[])) 12 []) at c
  rw [cStore,List.length_append] at c
  convert a.sequence (b.sequence c) using 1
  omega

theorem extract_executes (rows : List (List Rat)) (values : List Rat) (column : Nat)
    (selected : List.Forall₂ (fun row value => row[column]?=some value) rows values)
    (limit : Nat) (bounded : ∀ row∈rows,(Encoding.rationalRow.encode row).length ≤ limit) :
    ∃ time ≤ 10*rows.length.bits.length+7+1+
        (rows.length*(100*(limit+column+2)+2)+1+1+
          (8*(Encoding.sequence (Encoding.framed Encoding.rational) values).length+
            12*(Encoding.natural.encode rows.length).length+11)),
      Executes extract (state (Encoding.rationalMatrix.encode rows) [] column (List.replicate rows.length true) []) time
        (state [] (Encoding.rationalRow.encode values) column [] []) := by
  have a := readHeader_executes rows column
  obtain ⟨loopTime,loopBound,b⟩ := loop_executes rows values column selected limit bounded [] []
    (Encoding.natural.encode rows.length)
  simp only [List.append_nil] at b
  have c := finish_executes [] (Encoding.sequence (Encoding.framed Encoding.rational) values)
    (Encoding.natural.encode rows.length) column
  have final : Encoding.natural.encode rows.length++Encoding.sequence (Encoding.framed Encoding.rational) values=
      Encoding.rationalRow.encode values := by
    rw [selected.length_eq]
    rfl
  rw [final] at c
  exact ⟨_,by omega,a.sequence (b.sequence c)⟩

end Counting.StackMachine.GaussianRhs
