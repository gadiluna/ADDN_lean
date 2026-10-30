import Counting.StackRealizabilityArcRead
import Counting.StackDagClean
import Counting.RealizabilityCompactFields

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

def arcFlagRegisters (index : Fin 12) : Fin 32:=⟨12+index.val,by omega⟩
def arcFlagCells : List (Fin 32):=List.ofFn arcFlagRegisters

theorem arcFlagCells_mem (r : Fin 32) : r∈arcFlagCells ↔ 12≤r.val ∧ r.val<24:=by
  simp only [arcFlagCells,List.mem_ofFn]
  constructor
  · rintro ⟨i,rfl⟩;simp only [arcFlagRegisters];omega
  · intro bounds
    refine ⟨⟨r.val-12,by omega⟩,?_⟩
    apply Fin.ext
    dsimp only [arcFlagRegisters]
    omega

def arcPointValue (store : Store 30) : Bool:=GraphExpr.eval (arcReadValues store) GraphExpr.arc

def arcPoint : Routine 30:=sequence arcRead
  (sequence (GraphExpr.compile arcFlagRegisters 24 GraphExpr.arc) (clearRegisters arcFlagCells))

theorem arcPoint_executes (store : Store 30)
    (flags : ∀r : Fin 32,12≤r.val → r.val<24 → store r=[])
    (e26 : store 26=[]) (e27 : store 27=[]) (e28 : store 28=[]) :
    ∃ time ≤ 1000*arcReadSize store,
      Executes arcPoint store time (Function.update store 24 (arcPointValue store::store 24)):=by
  obtain ⟨readTime,readBound,reading⟩:=arcRead_executes store e26 e27 e28
  let read:=arcReadStore store
  have separate (i : Fin 12) : arcFlagRegisters i≠(24:Fin 32):=by
    intro same
    have value:=congrArg Fin.val same
    dsimp only [arcFlagRegisters] at value
    omega
  have contents (i : Fin 12) : read (arcFlagRegisters i)=arcReadValues store i::[]:=by
    dsimp only [read,arcFlagRegisters]
    rw [arcReadStore_flags]
    have empty : store (⟨12+i.val,by omega⟩:Fin 32)=[]:=flags _ (by dsimp;omega) (by dsimp;omega)
    rw [empty]
  have evaluating:=GraphExpr.compile_executes arcFlagRegisters 24 separate GraphExpr.arc
    (arcReadValues store) read (fun _=>[]) contents
  have outputAt : read 24=store 24:=by simp [read,arcReadStore]
  rw [outputAt] at evaluating
  let evaluated:=Function.update read 24 (arcPointValue store::store 24)
  have clearBound (r : Fin 32) (inside : r∈arcFlagCells) : (evaluated r).length≤1:=by
    obtain ⟨lo,hi⟩:=arcFlagCells_mem r |>.mp inside
    have different : r≠24:=by intro equal;subst r;simp at hi
    simp [evaluated,Function.update_of_ne different,read,arcReadStore,lo,hi,flags r lo hi]
  obtain ⟨clearTime,timeBound,clearing⟩:=DagValidation.clear_selected_executes arcFlagCells evaluated 1 clearBound
  have final : clearedStore arcFlagCells evaluated=
      Function.update store 24 (arcPointValue store::store 24):=by
    funext r
    by_cases output : r=24
    · subst r;simp [clearedStore,arcFlagCells_mem,evaluated]
    · by_cases inside : 12≤r.val ∧ r.val<24
      · simp [clearedStore,arcFlagCells_mem,inside,output,flags r inside.1 inside.2]
      · simp [clearedStore,arcFlagCells_mem,inside,evaluated,output,read,arcReadStore]
  rw [final] at clearing
  change clearTime≤12*(1+2) at timeBound
  have execution:=reading.sequence (evaluating.sequence clearing)
  change Executes arcPoint store (readTime+1+(121+1+clearTime)) _ at execution
  have positive : 1≤arcReadSize store:=by unfold arcReadSize;omega
  exact ⟨_,by omega,execution⟩

/-- The two matrix indices differ deliberately: incoming is receiver/sender,
while the output adjacency matrix is sender/receiver. -/
theorem arcPointValue_fields (store : Store 30) (size : Nat) (x y : Fin size)
    (atX : (store 8).length=x.val) (atY : (store 9).length=y.val)
    (atXY : (store 10).length=x.val*size+y.val)
    (atYX : (store 11).length=y.val*size+x.val) :
    arcPointValue store=RealizabilityVerifier.CompactGraph.fieldsArc
      (RealizabilityVerifier.CompactGraph.fieldsFromBits size (store 0) (store 1) (store 2)
        (store 3) (store 4) (store 5) (store 6) (store 7)) x y:=by
  simp only [arcPointValue,GraphExpr.eval_arc,arcReadValues,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    atX,atY,atXY,atYX]
  rfl

end Counting.StackMachine.RealizabilityCheck
