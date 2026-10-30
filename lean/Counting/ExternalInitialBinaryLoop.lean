import Counting.ExternalInitialBinaryCell
import Counting.ExternalTransitionRow
import Counting.StackRoutineFixedPrefix

namespace Counting.External.CookLevin.StackGenerator
open StackMachine StackMachine.Routine Tableau InitialRows

def initialBinaryChunk {time width : Nat} (setup : Setup width) (program : Machine.Program) (place : Nat) : List Bool :=
  if h : place<setup.capacity-1 then Encoding.sequence clauseCodec
    ((initialConstraint (T:=time) (setup.binary program (adjacentLeft setup.capacity ⟨place,h⟩)
      (adjacentRight setup.capacity ⟨place,h⟩))).toCNF.map (List.map CNFEncoding.literalRaw)) else []

structure InitialBinaryInvariant (w : InitialWorkspace extra) {width : Nat} (setup : Setup width)
    (store : Fin (extra+24) → List Bool) : Prop where
  offset : store (w 1)=List.replicate setup.offset.val true
  header : store (w 2)=setup.header
  canonical : store (w 0)=List.replicate (store (w 0)).length true
  bounded : (store (w 0)).length≤setup.capacity-1
  empty : ∀ i ∈ ([6,17,18,19,20] : List (Fin 24)), store (w i)=[]

theorem InitialBinaryInvariant.consume (w : InitialWorkspace extra) {width : Nat} (setup : Setup width)
    (store : Fin (extra+24) → List Bool) (valid : InitialBinaryInvariant w setup store) :
    InitialBinaryInvariant w setup (consume (w 0) store) := by
  constructor
  · simpa [Routine.consume,w.injective.eq_iff] using valid.offset
  · simpa [Routine.consume,w.injective.eq_iff] using valid.header
  · simp only [Routine.consume,Function.update_self]
    rw [valid.canonical,List.tail_replicate,List.length_replicate]
  · simp only [Routine.consume,Function.update_self,List.length_tail]
    exact (Nat.sub_le _ _).trans valid.bounded
  · intro i hi
    have different : i ≠ 0 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl <;> decide
    simpa [Routine.consume,w.injective.eq_iff,different] using valid.empty i hi

theorem InitialBinaryInvariant.emit (w : InitialWorkspace extra) {width : Nat} (setup : Setup width)
    (chunk : Nat → List Bool) (store : Fin (extra+24) → List Bool) (valid : InitialBinaryInvariant w setup store) :
    InitialBinaryInvariant w setup (emitBody (w 0) (w 5) chunk store) := by
  constructor
  · simpa [emitBody,w.injective.eq_iff] using valid.offset
  · simpa [emitBody,w.injective.eq_iff] using valid.header
  · simpa [emitBody,w.injective.eq_iff] using valid.canonical
  · simpa [emitBody,w.injective.eq_iff] using valid.bounded
  · intro i hi
    have different : i ≠ 5 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl <;> decide
    simpa [emitBody,w.injective.eq_iff,different] using valid.empty i hi

def initialBinaryRowLoop (extra : Nat) (w : InitialWorkspace extra) (program : Machine.Program) : Routine (extra+22) :=
  forEach (w 0) (initialBinaryCell extra w program)

theorem initialBinaryRowLoop_executes (extra : Nat) (w : InitialWorkspace extra) (program : Machine.Program)
    {time width : Nat} (setup : Setup width) (store : Fin (extra+24) → List Bool)
    (valid : InitialBinaryInvariant w setup store) :
    ∃ transitions ≤ (store (w 0)).length*((initialBinaryCoefficient program+17)*(width+1)^2+2)+1,
      Executes (initialBinaryRowLoop extra w program) store transitions
        (Function.update (Function.update store (w 0) []) (w 5)
          (emittedChunks (initialBinaryChunk (time:=time) setup program) (store (w 0)).length++store (w 5))) := by
  have body : ∀ state, InitialBinaryInvariant w setup state → state (w 0) ≠ [] →
      ∃ transitions ≤ (initialBinaryCoefficient program+17)*(width+1)^2,
        Executes (initialBinaryCell extra w program) (consume (w 0) state) transitions
          (emitBody (w 0) (w 5) (initialBinaryChunk (time:=time) setup program) (consume (w 0) state)) := by
    intro state invariant nonempty
    have consumed := invariant.consume
    let position := (consume (w 0) state (w 0)).length
    have positive : 0<(state (w 0)).length := List.length_pos_iff.mpr nonempty
    have positionBound : position<setup.capacity-1 := by
      dsimp only [position]
      simp only [Routine.consume,Function.update_self,List.length_tail]
      have := invariant.bounded
      omega
    obtain ⟨transitions,bound,run⟩ := initialBinaryCell_executes extra w program position setup.offset.val
      (consume (w 0) state) consumed.canonical consumed.offset consumed.empty
    rw [consumed.header] at bound run
    refine ⟨transitions,bound.trans (initialBinaryCellBound_polynomial program setup ⟨position,positionBound⟩),?_⟩
    rw [initialBinaryBytes_eq (time:=time) setup program ⟨position,positionBound⟩] at run
    simpa only [emitBody,initialBinaryChunk,dif_pos positionBound,position] using run
  exact descendingEmit_afterConsume (w 0) (w 5) (by simp [w.injective.eq_iff])
    (initialBinaryCell extra w program) (initialBinaryChunk (time:=time) setup program) (InitialBinaryInvariant w setup)
    ((initialBinaryCoefficient program+17)*(width+1)^2) body
    (InitialBinaryInvariant.consume w setup) (InitialBinaryInvariant.emit w setup _) store valid

def initialBinaryRow (extra : Nat) (w : InitialWorkspace extra) (program : Machine.Program) : Routine (extra+22) :=
  sequence (ofProgram (ListPrograms.copyProgram (extra+21) (w 3) (w 0) (w 20)))
    (sequence (discardBit (w 0)) (initialBinaryRowLoop extra w program))

def initialBinaryRowBound (program : Machine.Program) (width capacity : Nat) :=
  5*capacity+6+(capacity-1)*((initialBinaryCoefficient program+17)*(width+1)^2+2)

theorem initialBinaryRow_executes (extra : Nat) (w : InitialWorkspace extra) (program : Machine.Program)
    {time width : Nat} (setup : Setup width) (store : Fin (extra+24) → List Bool)
    (offsetValue : store (w 1)=List.replicate setup.offset.val true) (headerValue : store (w 2)=setup.header)
    (capacityValue : store (w 3)=List.replicate setup.capacity true) (placeEmpty : store (w 0)=[])
    (empty : ∀ i ∈ ([6,17,18,19,20] : List (Fin 24)), store (w i)=[]) :
    ∃ transitions ≤ initialBinaryRowBound program width setup.capacity,
      Executes (initialBinaryRow extra w program) store transitions
        (Function.update store (w 5)
          ((List.finRange (setup.capacity-1)).flatMap (fun place => Encoding.sequence clauseCodec
            ((initialConstraint (T:=time) (setup.binary program (adjacentLeft setup.capacity place)
              (adjacentRight setup.capacity place))).toCNF.map (List.map CNFEncoding.literalRaw)))++store (w 5))) := by
  let copied := Function.update store (w 0) (List.replicate setup.capacity true)
  let shortened := Function.update store (w 0) (List.replicate (setup.capacity-1) true)
  have copy : Executes (ofProgram (ListPrograms.copyProgram (extra+21) (w 3) (w 0) (w 20))) store
      (5*setup.capacity+2) copied := by
    simpa +instances only [ListPrograms.copyProgram,capacityValue,placeEmpty,List.append_nil,List.length_replicate,copied] using
      copy_executes (extra+21) (w 3) (w 0) (w 20)
        (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) store (empty 20 (by simp))
  have pop : Executes (discardBit (w 0)) copied 1 shortened := by
    simpa only [copied,shortened,Function.update_self,Function.update_idem,List.tail_replicate] using discardBit_executes (w 0) copied
  have valid : InitialBinaryInvariant w setup shortened := by
    constructor
    · simpa [shortened,w.injective.eq_iff] using offsetValue
    · simpa [shortened,w.injective.eq_iff] using headerValue
    · simp [shortened]
    · simp [shortened]
    · intro i hi
      have different : i ≠ 0 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl|rfl|rfl|rfl|rfl <;> decide
      simpa [shortened,w.injective.eq_iff,different] using empty i hi
  obtain ⟨loopTime,loopBound,loopRun⟩ := initialBinaryRowLoop_executes extra w program (time:=time) setup shortened valid
  have combined := copy.sequence (pop.sequence loopRun)
  refine ⟨5*setup.capacity+2+1+(1+1+loopTime),?_,?_⟩
  · simp only [shortened,Function.update_self,List.length_replicate] at loopBound
    unfold initialBinaryRowBound
    omega
  · have restored : Function.update shortened (w 0) []=store := by
      simp only [shortened,Function.update_idem,← placeEmpty,Function.update_eq_self]
    have chunkEquality : emittedChunks (initialBinaryChunk (time:=time) setup program) (setup.capacity-1)=
        (List.finRange (setup.capacity-1)).flatMap (fun place => Encoding.sequence clauseCodec
          ((initialConstraint (T:=time) (setup.binary program (adjacentLeft setup.capacity place)
            (adjacentRight setup.capacity place))).toCNF.map (List.map CNFEncoding.literalRaw))) := by
      unfold initialBinaryChunk
      exact emittedChunks_finRange (setup.capacity-1) (fun place => Encoding.sequence clauseCodec
        ((initialConstraint (T:=time) (setup.binary program (adjacentLeft setup.capacity place)
          (adjacentRight setup.capacity place))).toCNF.map (List.map CNFEncoding.literalRaw)))
    simpa +instances only [initialBinaryRow,ListPrograms.copyProgram,restored,chunkEquality,
      shortened,Function.update_self,List.length_replicate,Function.update_of_ne (show w 5 ≠ w 0 by simp [w.injective.eq_iff])] using combined

end Counting.External.CookLevin.StackGenerator
