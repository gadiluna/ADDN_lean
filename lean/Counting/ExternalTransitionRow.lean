import Counting.ExternalTransitionCellCost
import Counting.StackBoundedConsumeLoop
import Counting.ExternalOneHotLayout

namespace Counting.External.CookLevin.StackGenerator
open StackMachine StackMachine.Routine Tableau

def transitionChunk (program : Machine.Program) {time width : Nat} (round : Fin time) (place : Nat) : List Bool :=
  if h : place<width then Encoding.sequence clauseCodec
    ((transitionConstraint (Cellular.dynamics program (finRotate width)) round ⟨place,h⟩).toCNF.map
      (List.map CNFEncoding.literalRaw)) else []

structure RowInvariant (w : CoordinateWorkspace extra) (round width : Nat)
    (store : Fin (extra+12) → List Bool) : Prop where
  row : store (w 0)=List.replicate round true
  widthValue : store (w 1)=List.replicate width true
  canonical : store (w 2)=List.replicate (store (w 2)).length true
  bounded : (store (w 2)).length≤width
  empty : ∀ i ∈ ([3,4,5,6,8,9,11] : List (Fin 12)), store (w i)=[]

theorem RowInvariant.consume (w : CoordinateWorkspace extra) (round width : Nat)
    (store : Fin (extra+12) → List Bool) (valid : RowInvariant w round width store) :
    RowInvariant w round width (consume (w 2) store) := by
  constructor
  · simpa [Routine.consume,w.injective.eq_iff] using valid.row
  · simpa [Routine.consume,w.injective.eq_iff] using valid.widthValue
  · simp only [Routine.consume,Function.update_self]
    rw [valid.canonical,List.tail_replicate,List.length_replicate]
  · simp only [Routine.consume,Function.update_self,List.length_tail]
    exact (Nat.sub_le _ _).trans valid.bounded
  · intro i hi
    have different : i ≠ 2 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    simpa [Routine.consume,w.injective.eq_iff,different] using valid.empty i hi

theorem RowInvariant.emit (w : CoordinateWorkspace extra) (round width : Nat)
    (chunk : Nat → List Bool) (store : Fin (extra+12) → List Bool) (valid : RowInvariant w round width store) :
    RowInvariant w round width (emitBody (w 2) (w 7) chunk store) := by
  constructor
  · simpa [emitBody,w.injective.eq_iff] using valid.row
  · simpa [emitBody,w.injective.eq_iff] using valid.widthValue
  · simpa [emitBody,w.injective.eq_iff] using valid.canonical
  · simpa [emitBody,w.injective.eq_iff] using valid.bounded
  · intro i hi
    have different : i ≠ 7 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    simpa [emitBody,w.injective.eq_iff,different] using valid.empty i hi

def transitionRowLoop (extra : Nat) (w : CoordinateWorkspace extra) (program : Machine.Program) : Routine (extra+10) :=
  forEach (w 2) (transitionCell extra w program)

theorem transitionRowLoop_executes (extra : Nat) (w : CoordinateWorkspace extra) (program : Machine.Program)
    {time width : Nat} (round : Fin time) (store : Fin (extra+12) → List Bool)
    (valid : RowInvariant w round.val width store) :
    ∃ transitions ≤ (store (w 2)).length*(transitionCellCoefficient program*((time+1)*width+1)^2+2)+1,
      Executes (transitionRowLoop extra w program) store transitions
        (Function.update (Function.update store (w 2) []) (w 7)
          (emittedChunks (@transitionChunk program time width round) (store (w 2)).length++store (w 7))) := by
  have body : ∀ state, RowInvariant w round.val width state → state (w 2) ≠ [] →
      ∃ transitions ≤ transitionCellCoefficient program*((time+1)*width+1)^2,
        Executes (transitionCell extra w program) (consume (w 2) state) transitions
          (emitBody (w 2) (w 7) (@transitionChunk program time width round) (consume (w 2) state)) := by
    intro state invariant nonempty
    have consumed := invariant.consume
    let position := (consume (w 2) state (w 2)).length
    have positive : 0<(state (w 2)).length := List.length_pos_iff.mpr nonempty
    have positionBound : position<width := by
      dsimp only [position]
      simp only [Routine.consume,Function.update_self,List.length_tail]
      have := invariant.bounded
      omega
    obtain ⟨transitions,bound,run⟩ := transitionCell_executes extra w program round ⟨position,positionBound⟩
      (consume (w 2) state) consumed.row consumed.widthValue consumed.canonical consumed.empty
    refine ⟨transitions,bound.trans (transitionCellBound_polynomial program round ⟨position,positionBound⟩),?_⟩
    simpa only [emitBody,transitionChunk,dif_pos positionBound,position] using run
  exact descendingEmit_afterConsume (w 2) (w 7) (by simp [w.injective.eq_iff])
    (transitionCell extra w program) (@transitionChunk program time width round) (RowInvariant w round.val width)
    (transitionCellCoefficient program*((time+1)*width+1)^2) body
    (RowInvariant.consume w round.val width) (RowInvariant.emit w round.val width _) store valid

theorem emittedChunks_finRange (width : Nat) (chunk : Fin width → List Bool) :
    emittedChunks (fun place => if h : place<width then chunk ⟨place,h⟩ else []) width=
      (List.finRange width).flatMap chunk := by
  rw [emittedChunks,← finRange_values width,List.flatMap_map]
  apply congrArg (fun f => (List.finRange width).flatMap f)
  funext place
  simp [place.isLt]

def transitionRow (extra : Nat) (w : CoordinateWorkspace extra) (program : Machine.Program) : Routine (extra+10) :=
  sequence (ofProgram (ListPrograms.copyProgram (extra+9) (w 1) (w 2) (w 11))) (transitionRowLoop extra w program)

def transitionRowBound (program : Machine.Program) (time width : Nat) :=
  5*width+4+width*(transitionCellCoefficient program*((time+1)*width+1)^2+2)

theorem transitionRow_executes (extra : Nat) (w : CoordinateWorkspace extra) (program : Machine.Program)
    {time width : Nat} (round : Fin time) (store : Fin (extra+12) → List Bool)
    (roundValue : store (w 0)=List.replicate round.val true)
    (widthValue : store (w 1)=List.replicate width true) (placeEmpty : store (w 2)=[])
    (empty : ∀ i ∈ ([3,4,5,6,8,9,11] : List (Fin 12)), store (w i)=[]) :
    ∃ transitions ≤ transitionRowBound program time width,
      Executes (transitionRow extra w program) store transitions
        (Function.update store (w 7)
          ((List.finRange width).flatMap (fun place => Encoding.sequence clauseCodec
            ((transitionConstraint (Cellular.dynamics program (finRotate width)) round place).toCNF.map
              (List.map CNFEncoding.literalRaw)))++store (w 7))) := by
  let copied := Function.update store (w 2) (List.replicate width true)
  have copy : Executes (ofProgram (ListPrograms.copyProgram (extra+9) (w 1) (w 2) (w 11))) store
      (5*width+2) copied := by
    simpa +instances only [ListPrograms.copyProgram,widthValue,placeEmpty,List.append_nil,List.length_replicate,copied] using
      copy_executes (extra+9) (w 1) (w 2) (w 11)
        (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) store (empty 11 (by simp))
  have valid : RowInvariant w round.val width copied := by
    constructor
    · simpa [copied,w.injective.eq_iff] using roundValue
    · simpa [copied,w.injective.eq_iff] using widthValue
    · simp [copied]
    · simp [copied]
    · intro i hi
      have different : i ≠ 2 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
      simpa [copied,w.injective.eq_iff,different] using empty i hi
  obtain ⟨loopTime,loopBound,loopRun⟩ := transitionRowLoop_executes extra w program round copied valid
  have combined := copy.sequence loopRun
  refine ⟨5*width+2+1+loopTime,?_,?_⟩
  · simp only [copied,Function.update_self,List.length_replicate] at loopBound
    unfold transitionRowBound
    omega
  · have restored : Function.update copied (w 2) []=store := by
      simp only [copied,Function.update_idem,← placeEmpty,Function.update_eq_self]
    have chunkEquality : emittedChunks (@transitionChunk program time width round) width=
        (List.finRange width).flatMap (fun place => Encoding.sequence clauseCodec
          ((transitionConstraint (Cellular.dynamics program (finRotate width)) round place).toCNF.map
            (List.map CNFEncoding.literalRaw))) := by
      unfold transitionChunk
      exact emittedChunks_finRange width (fun place => Encoding.sequence clauseCodec
        ((transitionConstraint (Cellular.dynamics program (finRotate width)) round place).toCNF.map
          (List.map CNFEncoding.literalRaw)))
    simpa +instances only [transitionRow,ListPrograms.copyProgram,restored,chunkEquality,
      copied,Function.update_self,List.length_replicate,Function.update_of_ne (show w 7 ≠ w 2 by simp [w.injective.eq_iff])] using combined

end Counting.External.CookLevin.StackGenerator
