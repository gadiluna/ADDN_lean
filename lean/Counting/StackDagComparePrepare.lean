import Counting.StackDagKeyBounds

namespace Counting.StackMachine.DagUpdate.Key
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

def prepareKeys : Routine 62 := sequence encodeKey
  (sequence (move 61 3 50 49) (sequence (move 61 1 0 49)
    (sequence encodeKey (move 61 3 51 49))))

def preparedKeys (store : Store 62) (left right : Executable.Node) : Store 62 :=
  Function.update (Function.update (Function.update (Function.update store 0 []) 1 [])
    50 (Encoding.sequence Encoding.natural left.key)) 51 (Encoding.sequence Encoding.natural right.key)

def prepareKeysCost (left right : Executable.Node) : Nat :=
  keyBudget left+keyBudget right+
    6*((Encoding.sequence Encoding.natural left.key).length+(Encoding.node.encode right).length+
      (Encoding.sequence Encoding.natural right.key).length)+16

theorem prepareKeys_executes (store : Store 62) (left right : Executable.Node)
    (leftAt : store 0=Encoding.node.encode left) (rightAt : store 1=Encoding.node.encode right)
    (empty : ∀ r : Fin 64,r=3 ∨ (40≤r.val ∧ r.val≤44) ∨ (49≤r.val ∧ r.val≤51) → store r=[]) :
    Executes prepareKeys store (prepareKeysCost left right) (preparedKeys store left right) := by
  have first := encodeKey_executes store left leftAt (by
    intro r allowed
    apply empty r
    rcases allowed with h|h|h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · subst r;decide)
  let encodedLeft := Function.update (Function.update store 0 []) 3 (Encoding.sequence Encoding.natural left.key)
  have save := move_executes 61 (3:Fin 64) 50 49 (by decide) (by decide) (by decide)
    encodedLeft (by simp [encodedLeft,empty])
  have leftKey : encodedLeft 3=Encoding.sequence Encoding.natural left.key := by simp [encodedLeft]
  have firstTarget : encodedLeft 50=[] := by simp [encodedLeft,empty]
  rw [leftKey,firstTarget,List.append_nil] at save
  let saved := Function.update (Function.update encodedLeft 50 (Encoding.sequence Encoding.natural left.key)) 3 []
  have load := move_executes 61 (1:Fin 64) 0 49 (by decide) (by decide) (by decide)
    saved (by simp [saved,encodedLeft,empty])
  have secondNode : saved 1=Encoding.node.encode right := by simp [saved,encodedLeft,rightAt]
  have secondTarget : saved 0=[] := by simp [saved,encodedLeft]
  rw [secondNode,secondTarget,List.append_nil] at load
  let loaded := Function.update (Function.update saved 0 (Encoding.node.encode right)) 1 []
  have second := encodeKey_executes loaded right (by simp [loaded]) (by
    intro r allowed
    fin_cases r <;> simp_all [loaded,saved,encodedLeft])
  let encodedRight := Function.update (Function.update loaded 0 []) 3 (Encoding.sequence Encoding.natural right.key)
  have saveRight := move_executes 61 (3:Fin 64) 51 49 (by decide) (by decide) (by decide)
    encodedRight (by simp [encodedRight,loaded,saved,encodedLeft,empty])
  have rightKey : encodedRight 3=Encoding.sequence Encoding.natural right.key := by simp [encodedRight]
  have lastTarget : encodedRight 51=[] := by simp [encodedRight,loaded,saved,encodedLeft,empty]
  rw [rightKey,lastTarget,List.append_nil] at saveRight
  have final : Function.update (Function.update encodedRight 51 (Encoding.sequence Encoding.natural right.key)) 3 []=
      preparedKeys store left right := by
    funext r
    fin_cases r <;> simp [preparedKeys,encodedRight,loaded,saved,encodedLeft,empty]
  rw [final] at saveRight
  convert first.sequence (save.sequence (load.sequence (second.sequence saveRight))) using 1 <;>
    first | rfl | (dsimp only [prepareKeysCost];omega)

end Counting.StackMachine.DagUpdate.Key
