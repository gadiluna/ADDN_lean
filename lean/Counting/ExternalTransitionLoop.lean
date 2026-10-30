import Counting.ExternalTransitionRow

namespace Counting.External.CookLevin.StackGenerator
open StackMachine StackMachine.Routine Tableau

def transitionRowsChunk (program : Machine.Program) (time width round : Nat) : List Bool :=
  if h : round<time then (List.finRange width).flatMap (fun place => Encoding.sequence clauseCodec
    ((transitionConstraint (Cellular.dynamics program (finRotate width)) ⟨round,h⟩ place).toCNF.map
      (List.map CNFEncoding.literalRaw))) else []

structure RowsInvariant (w : CoordinateWorkspace extra) (time width : Nat)
    (store : Fin (extra+12) → List Bool) : Prop where
  widthValue : store (w 1)=List.replicate width true
  canonical : store (w 0)=List.replicate (store (w 0)).length true
  bounded : (store (w 0)).length≤time
  empty : ∀ i ∈ ([2,3,4,5,6,8,9,11] : List (Fin 12)), store (w i)=[]

theorem RowsInvariant.consume (w : CoordinateWorkspace extra) (time width : Nat)
    (store : Fin (extra+12) → List Bool) (valid : RowsInvariant w time width store) :
    RowsInvariant w time width (Routine.consume (w 0) store) := by
  constructor
  · simpa [Routine.consume,w.injective.eq_iff] using valid.widthValue
  · simp only [Routine.consume,Function.update_self]
    rw [valid.canonical,List.tail_replicate,List.length_replicate]
  · simp only [Routine.consume,Function.update_self,List.length_tail]
    exact (Nat.sub_le _ _).trans valid.bounded
  · intro i hi
    have different : i ≠ 0 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    simpa [Routine.consume,w.injective.eq_iff,different] using valid.empty i hi

theorem RowsInvariant.emit (w : CoordinateWorkspace extra) (time width : Nat)
    (chunk : Nat → List Bool) (store : Fin (extra+12) → List Bool) (valid : RowsInvariant w time width store) :
    RowsInvariant w time width (emitBody (w 0) (w 7) chunk store) := by
  constructor
  · simpa [emitBody,w.injective.eq_iff] using valid.widthValue
  · simpa [emitBody,w.injective.eq_iff] using valid.canonical
  · simpa [emitBody,w.injective.eq_iff] using valid.bounded
  · intro i hi
    have different : i ≠ 7 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    simpa [emitBody,w.injective.eq_iff,different] using valid.empty i hi

/-- Both dimensions are runtime unary inputs. The finite-control program
is fixed by the verifier; no formula or dimension-dependent lookup is an oracle. -/
def transitionsRoutine (extra : Nat) (w : CoordinateWorkspace extra) (program : Machine.Program) : Routine (extra+10) :=
  forEach (w 0) (transitionRow extra w program)

def transitionsBound (program : Machine.Program) (time width : Nat) := time*(transitionRowBound program time width+2)+1

theorem transitionsRoutine_executes (extra : Nat) (w : CoordinateWorkspace extra) (program : Machine.Program)
    (time width : Nat) (store : Fin (extra+12) → List Bool)
    (timeValue : store (w 0)=List.replicate time true)
    (widthValue : store (w 1)=List.replicate width true)
    (empty : ∀ i ∈ ([2,3,4,5,6,8,9,11] : List (Fin 12)), store (w i)=[]) :
    ∃ transitions ≤ transitionsBound program time width,
      Executes (transitionsRoutine extra w program) store transitions
        (Function.update (Function.update store (w 0) []) (w 7)
          ((List.finRange time).flatMap (fun round => (List.finRange width).flatMap (fun place => Encoding.sequence clauseCodec
            ((transitionConstraint (Cellular.dynamics program (finRotate width)) round place).toCNF.map
              (List.map CNFEncoding.literalRaw))))++store (w 7))) := by
  have body : ∀ state, RowsInvariant w time width state → state (w 0) ≠ [] →
      ∃ transitions ≤ transitionRowBound program time width,
        Executes (transitionRow extra w program) (Routine.consume (w 0) state) transitions
          (emitBody (w 0) (w 7) (transitionRowsChunk program time width) (Routine.consume (w 0) state)) := by
    intro state invariant nonempty
    have consumed := invariant.consume
    let round := (Routine.consume (w 0) state (w 0)).length
    have positive : 0<(state (w 0)).length := List.length_pos_iff.mpr nonempty
    have roundBound : round<time := by
      dsimp only [round]
      simp only [Routine.consume,Function.update_self,List.length_tail]
      have := invariant.bounded
      omega
    obtain ⟨transitions,bound,run⟩ := transitionRow_executes extra w program ⟨round,roundBound⟩
      (Routine.consume (w 0) state) consumed.canonical consumed.widthValue (consumed.empty 2 (by simp))
      (fun i hi => consumed.empty i (List.mem_cons_of_mem 2 hi))
    refine ⟨transitions,bound,?_⟩
    simpa only [emitBody,transitionRowsChunk,dif_pos roundBound,round] using run
  have valid : RowsInvariant w time width store := by
    exact ⟨widthValue,by simp [timeValue],by simp [timeValue],empty⟩
  obtain ⟨transitions,bound,run⟩ := descendingEmit_afterConsume (w 0) (w 7) (by simp [w.injective.eq_iff])
    (transitionRow extra w program) (transitionRowsChunk program time width) (RowsInvariant w time width)
    (transitionRowBound program time width) body
    (RowsInvariant.consume w time width) (RowsInvariant.emit w time width _) store valid
  refine ⟨transitions,?_,?_⟩
  · simpa only [transitionsBound,timeValue,List.length_replicate] using bound
  · have chunks : emittedChunks (transitionRowsChunk program time width) time=
        (List.finRange time).flatMap (fun round => (List.finRange width).flatMap (fun place => Encoding.sequence clauseCodec
          ((transitionConstraint (Cellular.dynamics program (finRotate width)) round place).toCNF.map
            (List.map CNFEncoding.literalRaw)))) := by
      unfold transitionRowsChunk
      exact emittedChunks_finRange time (fun round => (List.finRange width).flatMap (fun place => Encoding.sequence clauseCodec
        ((transitionConstraint (Cellular.dynamics program (finRotate width)) round place).toCNF.map
          (List.map CNFEncoding.literalRaw))))
    simpa only [transitionsRoutine,timeValue,List.length_replicate,chunks] using run

theorem transitionsBound_polynomial (program : Machine.Program) (time width : Nat) :
    transitionsBound program time width≤
      (transitionCellCoefficient program+20)*((time+1)*(width+1)+1)^4 := by
  let size := (time+1)*(width+1)
  let coefficient := transitionCellCoefficient program
  have ht : time≤size := by dsimp only [size]; nlinarith
  have hw : width≤size := by dsimp only [size]; nlinarith
  have hn : (time+1)*width≤size := by dsimp only [size]; nlinarith
  have power := Nat.pow_le_pow_left (Nat.add_le_add_right hn 1) 2
  have productBound := Nat.mul_le_mul ht hw
  have positive : 1≤(size+1)^4 := Nat.one_le_pow 4 _ (by omega)
  have bigPower : size^2*(size+1)^2≤(size+1)^4 := by nlinarith
  have weighted := Nat.mul_le_mul_left coefficient (Nat.mul_le_mul productBound power)
  have finalWeighted := Nat.mul_le_mul_left coefficient bigPower
  unfold transitionsBound transitionRowBound
  change time*(5*width+4+width*(transitionCellCoefficient program*((time+1)*width+1)^2+2)+2)+1≤
    (transitionCellCoefficient program+20)*(size+1)^4
  dsimp only [coefficient] at weighted finalWeighted
  have remainder : 7*size^2+6*size+1≤20*(size+1)^4 := by nlinarith
  nlinarith

end Counting.External.CookLevin.StackGenerator
