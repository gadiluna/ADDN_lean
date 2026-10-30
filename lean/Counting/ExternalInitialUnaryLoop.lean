import Counting.ExternalInitialLayout
import Counting.ExternalTransitionRow

namespace Counting.External.CookLevin.StackGenerator
open StackMachine StackMachine.Routine Tableau InitialRows

def initialUnaryChunk {time width : Nat} (setup : Setup width) (program : Machine.Program) (place : Nat) : List Bool :=
  if h : place<width then Encoding.sequence clauseCodec
    ((initialConstraint (T:=time) (setup.unary program ⟨place,h⟩)).toCNF.map (List.map CNFEncoding.literalRaw)) else []

structure InitialRowInvariant (w : InitialWorkspace extra) {width : Nat} (setup : Setup width)
    (store : Fin (extra+24) → List Bool) : Prop where
  offset : store (w 1)=List.replicate setup.offset.val true
  header : store (w 2)=setup.header
  capacity : store (w 3)=List.replicate setup.capacity true
  canonical : store (w 0)=List.replicate (store (w 0)).length true
  bounded : (store (w 0)).length≤width
  empty : ∀ i ∈ ([6,7,8,9,10,11,12,13,14,15,17,18,19,20] : List (Fin 24)), store (w i)=[]

theorem InitialRowInvariant.consume (w : InitialWorkspace extra) {width : Nat} (setup : Setup width)
    (store : Fin (extra+24) → List Bool) (valid : InitialRowInvariant w setup store) :
    InitialRowInvariant w setup (consume (w 0) store) := by
  constructor
  · simpa [Routine.consume,w.injective.eq_iff] using valid.offset
  · simpa [Routine.consume,w.injective.eq_iff] using valid.header
  · simpa [Routine.consume,w.injective.eq_iff] using valid.capacity
  · simp only [Routine.consume,Function.update_self]
    rw [valid.canonical,List.tail_replicate,List.length_replicate]
  · simp only [Routine.consume,Function.update_self,List.length_tail]
    exact (Nat.sub_le _ _).trans valid.bounded
  · intro i hi
    have different : i ≠ 0 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    simpa [Routine.consume,w.injective.eq_iff,different] using valid.empty i hi

theorem InitialRowInvariant.emit (w : InitialWorkspace extra) {width : Nat} (setup : Setup width)
    (chunk : Nat → List Bool) (store : Fin (extra+24) → List Bool) (valid : InitialRowInvariant w setup store) :
    InitialRowInvariant w setup (emitBody (w 0) (w 5) chunk store) := by
  constructor
  · simpa [emitBody,w.injective.eq_iff] using valid.offset
  · simpa [emitBody,w.injective.eq_iff] using valid.header
  · simpa [emitBody,w.injective.eq_iff] using valid.capacity
  · simpa [emitBody,w.injective.eq_iff] using valid.canonical
  · simpa [emitBody,w.injective.eq_iff] using valid.bounded
  · intro i hi
    have different : i ≠ 5 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    simpa [emitBody,w.injective.eq_iff,different] using valid.empty i hi

def initialUnaryRowLoop (extra : Nat) (w : InitialWorkspace extra) (program : Machine.Program) : Routine (extra+22) :=
  forEach (w 0) (initialCell extra w program)

theorem initialUnaryRowLoop_executes (extra : Nat) (w : InitialWorkspace extra) (program : Machine.Program)
    {time width : Nat} (setup : Setup width) (store : Fin (extra+24) → List Bool)
    (valid : InitialRowInvariant w setup store) :
    ∃ transitions ≤ (store (w 0)).length*((initialCoefficient program+213)*(width+1)^2+2)+1,
      Executes (initialUnaryRowLoop extra w program) store transitions
        (Function.update (Function.update store (w 0) []) (w 5)
          (emittedChunks (initialUnaryChunk (time:=time) setup program) (store (w 0)).length++store (w 5))) := by
  have body : ∀ state, InitialRowInvariant w setup state → state (w 0) ≠ [] →
      ∃ transitions ≤ (initialCoefficient program+213)*(width+1)^2,
        Executes (initialCell extra w program) (consume (w 0) state) transitions
          (emitBody (w 0) (w 5) (initialUnaryChunk (time:=time) setup program) (consume (w 0) state)) := by
    intro state invariant nonempty
    have consumed := invariant.consume
    let position := (consume (w 0) state (w 0)).length
    have positive : 0<(state (w 0)).length := List.length_pos_iff.mpr nonempty
    have positionBound : position<width := by
      dsimp only [position]
      simp only [Routine.consume,Function.update_self,List.length_tail]
      have := invariant.bounded
      omega
    obtain ⟨transitions,bound,run⟩ := initialCell_executes extra w program position setup.offset.val setup.capacity
      (consume (w 0) state) consumed.canonical consumed.offset consumed.capacity consumed.empty
    rw [consumed.header] at bound run
    refine ⟨transitions,bound.trans (initialCellBound_polynomial program setup ⟨position,positionBound⟩),?_⟩
    rw [initialBytes_eq (time:=time) setup program ⟨position,positionBound⟩] at run
    simpa only [emitBody,initialUnaryChunk,dif_pos positionBound,position] using run
  exact descendingEmit_afterConsume (w 0) (w 5) (by simp [w.injective.eq_iff])
    (initialCell extra w program) (initialUnaryChunk (time:=time) setup program) (InitialRowInvariant w setup)
    ((initialCoefficient program+213)*(width+1)^2) body
    (InitialRowInvariant.consume w setup) (InitialRowInvariant.emit w setup _) store valid

def initialUnaryRow (extra : Nat) (w : InitialWorkspace extra) (program : Machine.Program) : Routine (extra+22) :=
  sequence (ofProgram (ListPrograms.copyProgram (extra+21) (w 4) (w 0) (w 20))) (initialUnaryRowLoop extra w program)

def initialUnaryRowBound (program : Machine.Program) (width : Nat) :=
  5*width+4+width*((initialCoefficient program+213)*(width+1)^2+2)

theorem initialUnaryRow_executes (extra : Nat) (w : InitialWorkspace extra) (program : Machine.Program)
    {time width : Nat} (setup : Setup width) (store : Fin (extra+24) → List Bool)
    (offsetValue : store (w 1)=List.replicate setup.offset.val true) (headerValue : store (w 2)=setup.header)
    (capacityValue : store (w 3)=List.replicate setup.capacity true)
    (widthValue : store (w 4)=List.replicate width true) (placeEmpty : store (w 0)=[])
    (empty : ∀ i ∈ ([6,7,8,9,10,11,12,13,14,15,17,18,19,20] : List (Fin 24)), store (w i)=[]) :
    ∃ transitions ≤ initialUnaryRowBound program width,
      Executes (initialUnaryRow extra w program) store transitions
        (Function.update store (w 5)
          ((List.finRange width).flatMap (fun place => Encoding.sequence clauseCodec
            ((initialConstraint (T:=time) (setup.unary program place)).toCNF.map (List.map CNFEncoding.literalRaw)))++store (w 5))) := by
  let copied := Function.update store (w 0) (List.replicate width true)
  have copy : Executes (ofProgram (ListPrograms.copyProgram (extra+21) (w 4) (w 0) (w 20))) store
      (5*width+2) copied := by
    simpa +instances only [ListPrograms.copyProgram,widthValue,placeEmpty,List.append_nil,List.length_replicate,copied] using
      copy_executes (extra+21) (w 4) (w 0) (w 20)
        (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) store (empty 20 (by simp))
  have valid : InitialRowInvariant w setup copied := by
    constructor
    · simpa [copied,w.injective.eq_iff] using offsetValue
    · simpa [copied,w.injective.eq_iff] using headerValue
    · simpa [copied,w.injective.eq_iff] using capacityValue
    · simp [copied]
    · simp [copied]
    · intro i hi
      have different : i ≠ 0 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
      simpa [copied,w.injective.eq_iff,different] using empty i hi
  obtain ⟨loopTime,loopBound,loopRun⟩ := initialUnaryRowLoop_executes extra w program (time:=time) setup copied valid
  have combined := copy.sequence loopRun
  refine ⟨5*width+2+1+loopTime,?_,?_⟩
  · simp only [copied,Function.update_self,List.length_replicate] at loopBound
    unfold initialUnaryRowBound
    omega
  · have restored : Function.update copied (w 0) []=store := by
      simp only [copied,Function.update_idem,← placeEmpty,Function.update_eq_self]
    have chunkEquality : emittedChunks (initialUnaryChunk (time:=time) setup program) width=
        (List.finRange width).flatMap (fun place => Encoding.sequence clauseCodec
          ((initialConstraint (T:=time) (setup.unary program place)).toCNF.map (List.map CNFEncoding.literalRaw))) := by
      unfold initialUnaryChunk
      exact emittedChunks_finRange width (fun place => Encoding.sequence clauseCodec
        ((initialConstraint (T:=time) (setup.unary program place)).toCNF.map (List.map CNFEncoding.literalRaw)))
    simpa +instances only [initialUnaryRow,ListPrograms.copyProgram,restored,chunkEquality,
      copied,Function.update_self,List.length_replicate,Function.update_of_ne (show w 5 ≠ w 0 by simp [w.injective.eq_iff])] using combined

end Counting.External.CookLevin.StackGenerator
