import Counting.ExternalFinalLayout

namespace Counting.External.CookLevin.StackGenerator
open StackMachine StackMachine.Routine Tableau

def finalLiteralChunk (program : Machine.Program) (time width place : Nat) : List Bool :=
  Encoding.sequence literalCodec (shiftedLiterals (Cellular.alphabet program*(time*width+place)) (finalOffsets program))

def finalLiteralLoop (extra : Nat) (w : CoordinateWorkspace extra) (program : Machine.Program) : Routine (extra+10) :=
  forEach (w 2) (centeredLiterals extra w (Cellular.alphabet program) (finalOffsets program))

theorem finalLiteralLoop_executes (extra : Nat) (w : CoordinateWorkspace extra) (program : Machine.Program)
    (time width : Nat) (store : Fin (extra+12) → List Bool) (valid : RowInvariant w time width store) :
    ∃ transitions ≤ (store (w 2)).length*
        (centeredLiteralsCoefficient (Cellular.alphabet program) (finalOffsets program)*((time+1)*width+1)^2+2)+1,
      Executes (finalLiteralLoop extra w program) store transitions
        (Function.update (Function.update store (w 2) []) (w 7)
          (emittedChunks (finalLiteralChunk program time width) (store (w 2)).length++store (w 7))) := by
  have body : ∀ state, RowInvariant w time width state → state (w 2) ≠ [] →
      ∃ transitions ≤ centeredLiteralsCoefficient (Cellular.alphabet program) (finalOffsets program)*((time+1)*width+1)^2,
        Executes (centeredLiterals extra w (Cellular.alphabet program) (finalOffsets program)) (Routine.consume (w 2) state) transitions
          (emitBody (w 2) (w 7) (finalLiteralChunk program time width) (Routine.consume (w 2) state)) := by
    intro state invariant nonempty
    have consumed := invariant.consume
    let position := (Routine.consume (w 2) state (w 2)).length
    have positive : 0<(state (w 2)).length := List.length_pos_iff.mpr nonempty
    have positionBound : position<width := by
      dsimp only [position]
      simp only [Routine.consume,Function.update_self,List.length_tail]
      have := invariant.bounded
      omega
    have empty : ∀ i ∈ ([3,4,5,6,8,11] : List (Fin 12)), (Routine.consume (w 2) state) (w i)=[] := by
      intro i hi
      apply consumed.empty i
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl <;> simp
    obtain ⟨transitions,bound,run⟩ := centeredLiterals_executes extra w (Cellular.alphabet program) (finalOffsets program)
      time width position (Routine.consume (w 2) state) consumed.row consumed.widthValue consumed.canonical empty
    refine ⟨transitions,bound.trans (centeredLiteralsBound_polynomial _ _ time ⟨position,positionBound⟩),?_⟩
    exact run
  exact descendingEmit_afterConsume (w 2) (w 7) (by simp [w.injective.eq_iff])
    (centeredLiterals extra w (Cellular.alphabet program) (finalOffsets program)) (finalLiteralChunk program time width)
    (RowInvariant w time width)
    (centeredLiteralsCoefficient (Cellular.alphabet program) (finalOffsets program)*((time+1)*width+1)^2)
    body (RowInvariant.consume w time width) (RowInvariant.emit w time width _) store valid

theorem finalLiteralChunks_eq (program : Machine.Program) (time width : Nat) :
    emittedChunks (finalLiteralChunk program time width) width=
      Encoding.sequence literalCodec ((@finalClause time width (Cellular.alphabet program) (Cellular.accept program)).map CNFEncoding.literalRaw) := by
  rw [finalClause_raw,emittedChunks,← finRange_values width,List.flatMap_map]
  simp only [sequence_flatMap,List.flatMap_assoc,finalLiteralChunk]

def finalLiterals (extra : Nat) (w : CoordinateWorkspace extra) (program : Machine.Program) : Routine (extra+10) :=
  sequence (ofProgram (ListPrograms.copyProgram (extra+9) (w 1) (w 2) (w 11))) (finalLiteralLoop extra w program)

def finalLiteralsBound (program : Machine.Program) (time width : Nat) :=
  5*width+4+width*(centeredLiteralsCoefficient (Cellular.alphabet program) (finalOffsets program)*((time+1)*width+1)^2+2)

theorem finalLiterals_executes (extra : Nat) (w : CoordinateWorkspace extra) (program : Machine.Program)
    (time width : Nat) (store : Fin (extra+12) → List Bool)
    (timeValue : store (w 0)=List.replicate time true)
    (widthValue : store (w 1)=List.replicate width true) (placeEmpty : store (w 2)=[])
    (empty : ∀ i ∈ ([3,4,5,6,8,9,11] : List (Fin 12)), store (w i)=[]) :
    ∃ transitions ≤ finalLiteralsBound program time width,
      Executes (finalLiterals extra w program) store transitions
        (Function.update store (w 7)
          (Encoding.sequence literalCodec ((@finalClause time width (Cellular.alphabet program) (Cellular.accept program)).map CNFEncoding.literalRaw)++store (w 7))) := by
  let copied := Function.update store (w 2) (List.replicate width true)
  have copy : Executes (ofProgram (ListPrograms.copyProgram (extra+9) (w 1) (w 2) (w 11))) store
      (5*width+2) copied := by
    simpa +instances only [ListPrograms.copyProgram,widthValue,placeEmpty,List.append_nil,List.length_replicate,copied] using
      copy_executes (extra+9) (w 1) (w 2) (w 11)
        (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) store (empty 11 (by simp))
  have valid : RowInvariant w time width copied := by
    constructor
    · simpa [copied,w.injective.eq_iff] using timeValue
    · simpa [copied,w.injective.eq_iff] using widthValue
    · simp [copied]
    · simp [copied]
    · intro i hi
      have different : i ≠ 2 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
      simpa [copied,w.injective.eq_iff,different] using empty i hi
  obtain ⟨loopTime,loopBound,loopRun⟩ := finalLiteralLoop_executes extra w program time width copied valid
  have combined := copy.sequence loopRun
  refine ⟨5*width+2+1+loopTime,?_,?_⟩
  · simp only [copied,Function.update_self,List.length_replicate] at loopBound
    unfold finalLiteralsBound
    omega
  · have restored : Function.update copied (w 2) []=store := by
      simp only [copied,Function.update_idem,← placeEmpty,Function.update_eq_self]
    simpa +instances only [finalLiterals,ListPrograms.copyProgram,restored,finalLiteralChunks_eq,
      copied,Function.update_self,List.length_replicate,Function.update_of_ne (show w 7 ≠ w 2 by simp [w.injective.eq_iff])] using combined

end Counting.External.CookLevin.StackGenerator
