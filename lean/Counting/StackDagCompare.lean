import Counting.StackDagComparePrepare
import Counting.StackDagCompareKeys
import Counting.DagKeySize

namespace Counting.StackMachine.DagUpdate.Key
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

def compareNodes : Routine 62 := sequence prepareKeys compareKeys

def nodesComparisonResult (store : Store 62) (left right : Executable.Node) : Store 62 :=
  Function.update (Function.update (Function.update store 0 []) 1 [])
    2 [Executable.lexLE left.key right.key]

/-- The DAG signature comparator is implemented by physical serialization,
parsing and numeric comparisons. All fields remain binary. -/
theorem compareNodes_executes (store : Store 62) (left right : Executable.Node)
    (leftAt : store 0=Encoding.node.encode left) (rightAt : store 1=Encoding.node.encode right)
    (empty : ∀ r : Fin 64,(2≤r.val ∧ r.val≤13) ∨ (40≤r.val ∧ r.val≤44) ∨
      (49≤r.val ∧ r.val≤51) → store r=[]) :
    ∃ time≤10000*((store 0).length+(store 1).length+1)^2,
      Executes compareNodes store time (nodesComparisonResult store left right) := by
  have prepared := prepareKeys_executes store left right leftAt rightAt (by
    intro r allowed
    apply empty r
    rcases allowed with h|h|h
    · subst r;decide
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h))
  obtain ⟨time,bounded,compared⟩ := compareKeys_executes (preparedKeys store left right) left.key right.key
    (by simp [preparedKeys]) (by simp [preparedKeys]) (by
      intro r allowed
      fin_cases r <;> simp_all [preparedKeys])
  have final : Function.update (Function.update (Function.update (preparedKeys store left right) 50 []) 51 [])
      2 [Executable.lexLE left.key right.key]=nodesComparisonResult store left right := by
    funext r
    fin_cases r <;> simp [preparedKeys,nodesComparisonResult,empty]
  rw [final] at compared
  refine ⟨prepareKeysCost left right+1+time,?_,prepared.sequence compared⟩
  have costLeft := keyBudget_linear left
  have costRight := keyBudget_linear right
  have sizeLeft := Executable.sequence_key_length left
  have sizeRight := Executable.sequence_key_length right
  have sizes : (Encoding.sequence Encoding.natural left.key).length+
      (Encoding.sequence Encoding.natural right.key).length+1≤
      5*((Encoding.node.encode left).length+(Encoding.node.encode right).length+1) := by omega
  have squares : ((Encoding.sequence Encoding.natural left.key).length+
      (Encoding.sequence Encoding.natural right.key).length+1)^2≤
      (5*((Encoding.node.encode left).length+(Encoding.node.encode right).length+1))^2 := by
    gcongr
  simp only [preparedKeys,Function.update_self,Function.update_of_ne (show (50:Fin 64)≠51 by decide)] at bounded
  rw [leftAt,rightAt]
  unfold prepareKeysCost
  nlinarith

end Counting.StackMachine.DagUpdate.Key
