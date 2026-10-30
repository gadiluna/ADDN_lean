import Counting.StackRealizabilityArcPoint

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false

def arcTables (store : Store 30) (i : Fin 8) : List Bool:=store ⟨i.val,by omega⟩

def arcCell (tables : Fin 8→List Bool) (x y xy yx : Nat) : Bool:=
  (RealizabilityVerifier.BitGraph.bitAt (tables 0) x &&
    RealizabilityVerifier.BitGraph.bitAt (tables 1) y &&
    (RealizabilityVerifier.BitGraph.bitAt (tables 6) xy && RealizabilityVerifier.BitGraph.bitAt (tables 3) x)) ||
  (RealizabilityVerifier.BitGraph.bitAt (tables 1) x && RealizabilityVerifier.BitGraph.bitAt (tables 0) y &&
    RealizabilityVerifier.BitGraph.bitAt (tables 7) yx) ||
  (RealizabilityVerifier.BitGraph.bitAt (tables 2) x && RealizabilityVerifier.BitGraph.bitAt (tables 1) y &&
    RealizabilityVerifier.BitGraph.bitAt (tables 4) y) ||
  (RealizabilityVerifier.BitGraph.bitAt (tables 1) x && RealizabilityVerifier.BitGraph.bitAt (tables 2) y &&
    (RealizabilityVerifier.BitGraph.bitAt (tables 4) x || RealizabilityVerifier.BitGraph.bitAt (tables 5) x))

theorem arcPointValue_cell (store : Store 30) : arcPointValue store=
    arcCell (arcTables store) (store 8).length (store 9).length (store 10).length (store 11).length:=by
  rw [arcPointValue,GraphExpr.eval_arc]
  rfl

@[simp] theorem arcTables_update (store : Store 30) (r : Fin 32) (outside : 8≤r.val) (word : List Bool) :
    arcTables (Function.update store r word)=arcTables store:=by
  funext i
  unfold arcTables
  apply Function.update_of_ne
  intro same
  have equal:=congrArg Fin.val same
  change i.val=r.val at equal
  have bound:=i.isLt
  omega


def arcRowValues (tables : Fin 8→List Bool) (width x : Nat) : Nat→Nat→Nat→Nat→List Bool
  | _,_,_,0=>[]
  | y,xy,yx,count+1=>arcCell tables x y xy yx::arcRowValues tables width x (y+1) (xy+1) (yx+width) count

@[simp] theorem arcRowValues_length (tables : Fin 8→List Bool) (width x y xy yx count : Nat) :
    (arcRowValues tables width x y xy yx count).length=count:=by
  induction count generalizing y xy yx with
  | zero=>rfl
  | succ count ih=>simp [arcRowValues,ih]


def arcTableValues (tables : Fin 8→List Bool) (width : Nat) : Nat→Nat→Nat→List Bool
  | _,_,0=>[]
  | x,xy,count+1=>arcRowValues tables width x 0 xy x width++
      arcTableValues tables width (x+1) (xy+width) count

@[simp] theorem arcTableValues_length (tables : Fin 8→List Bool) (width x xy count : Nat) :
    (arcTableValues tables width x xy count).length=count*width:=by
  induction count generalizing x xy with
  | zero=>simp [arcTableValues]
  | succ count ih=>simp [arcTableValues,ih,Nat.add_mul,Nat.add_comm]


end Counting.StackMachine.RealizabilityCheck
