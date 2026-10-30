import Counting.StackAuditPropagationDownLoop
import Counting.StackAuditPropagationLevelBounds
import Counting.PropagationFoldBounds

namespace Counting.StackMachine.AuditPropagation

/-- Uniform cost of one level, in a fixed bound on the actual array word. -/
def downUniform (vista : Executable.Vista) (tableLength width : Nat) : Nat :=
  vista.nodes.size*(30000*(tableLength+(Encoding.vista.encode vista).length+
    8*(width+1)^2+3*vista.nodes.size+3)^5+2)+1+80*(vista.nodes.size+1)

theorem downItemBudget_uniform (vista : Executable.Vista) (r tableLength : Nat) (weights : Array Nat)
    (width : Nat) (sized : weights.size=vista.nodes.size) (below : r<vista.nodes.size)
    (codeBound : ((Encoding.array Encoding.natural).encode weights).length ≤ width) :
    downItemBudget vista r tableLength weights ≤ downUniform vista tableLength width := by
  have loop := levelLoopBudget_polynomial vista r tableLength 0 vista.nodes.size weights sized (by omega)
  have sz : r.size ≤ r := Nat.size_le.mpr Nat.lt_two_pow_self
  have sn : (r+1).size ≤ r+1 := Nat.size_le.mpr Nat.lt_two_pow_self
  have raised : (((Encoding.array Encoding.natural).encode weights).length+1)^2 ≤ (width+1)^2 :=
    Nat.pow_le_pow_left (by omega) 2
  have inner : tableLength+(Encoding.vista.encode vista).length+
      8*(((Encoding.array Encoding.natural).encode weights).length+1)^2+
      r.size+(r+1).size+vista.nodes.size+2 ≤
      tableLength+(Encoding.vista.encode vista).length+8*(width+1)^2+3*vista.nodes.size+3 := by omega
  have bounded := loop.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _
    (Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left inner 5)) 2)) 1)
  unfold downItemBudget downUniform
  omega

/-- The induction keeps one bound for all prefixes of the original run,
including the high-level prefixes that are not themselves propagateDown. -/
theorem downLoopBudget_uniform (vista : Executable.Vista) (tableLength rounds : Nat) (weights : Array Nat)
    (width : Nat) (sized : weights.size=vista.nodes.size) (depth : rounds ≤ vista.nodes.size)
    (prefixBound : ∀ levels : List Nat,levels.length ≤ rounds →
      ((Encoding.array Encoding.natural).encode (levels.foldl (Executable.propagateLevel vista) weights)).length ≤ width) :
    downLoopBudget vista tableLength rounds weights ≤ rounds*(downUniform vista tableLength width+2)+1 := by
  induction rounds generalizing weights with
  | zero => simp [downLoopBudget]
  | succ rounds ih =>
    have initial := prefixBound [] (by simp)
    change ((Encoding.array Encoding.natural).encode weights).length ≤ width at initial
    have headBound := downItemBudget_uniform vista rounds tableLength weights width sized (by omega) initial
    have tailBound := ih (Executable.propagateLevel vista weights rounds)
      ((Executable.propagateLevel_size vista rounds weights).trans sized) (by omega) (by
        intro levels short
        exact prefixBound (rounds::levels) (by simp only [List.length_cons];omega))
    change downItemBudget vista rounds tableLength weights+2+
      downLoopBudget vista tableLength rounds (Executable.propagateLevel vista weights rounds) ≤ _
    simp only [Nat.add_mul,Nat.one_mul]
    omega

/-- Complete descending propagation is polynomial in its initial encoded
weights and DAG when the explicit level count is bounded by stored nodes. -/
theorem downLoopBudget_polynomial (vista : Executable.Vista) (tableLength rounds : Nat) (weights : Array Nat)
    (sized : weights.size=vista.nodes.size) (depth : rounds ≤ vista.nodes.size) :
    downLoopBudget vista tableLength rounds weights ≤
      rounds*(downUniform vista tableLength
        (5*(((Encoding.array Encoding.natural).encode weights).length+1)^3)+2)+1 := by
  apply downLoopBudget_uniform vista tableLength rounds weights _ sized depth
  intro levels short
  exact Executable.propagateLevels_encoded_polynomial vista weights levels sized (short.trans depth)

end Counting.StackMachine.AuditPropagation
