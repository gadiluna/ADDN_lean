import Counting.StackAuditPropagationLevelLoop
import Counting.AuditPropagationLevelSize

namespace Counting.StackMachine.AuditPropagation

/-- Uniform bounds are supplied for prefixes of the original scan, avoiding
iteration of a polynomial bound on already-expanded intermediate encodings. -/
theorem levelLoopBudget_bound (vista : Executable.Vista) (r tableLength start count : Nat)
    (weights : Array Nat) (width : Nat)
    (prefixBound : ∀ j ≤ count,
      ((Encoding.array Encoding.natural).encode (levelScan vista r start j weights)).length ≤ width) :
    levelLoopBudget vista r tableLength start count weights ≤
      count*(30000*(tableLength+(Encoding.vista.encode vista).length+width+
        r.size+(r+1).size+start+count+2)^5+2)+1 := by
  induction count generalizing start weights with
  | zero => simp [levelLoopBudget]
  | succ count ih =>
    have tailPrefix (j : Nat) (small : j ≤ count) :
        ((Encoding.array Encoding.natural).encode
          (levelScan vista r (start+1) j (levelChoiceWeights vista r start weights))).length ≤ width := by
      exact prefixBound (j+1) (by omega)
    have tail := ih (start+1) (levelChoiceWeights vista r start weights) tailPrefix
    have initial := prefixBound 0 (by omega)
    change ((Encoding.array Encoding.natural).encode weights).length ≤ width at initial
    let base := tableLength+(Encoding.vista.encode vista).length+width+r.size+(r+1).size+start+(count+1)+2
    have headBound : 30000*(tableLength+(Encoding.vista.encode vista).length+
        ((Encoding.array Encoding.natural).encode weights).length+r.size+(r+1).size+start+2)^5 ≤ 30000*base^5 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp only [base];omega) 5)
    have sameBase : tableLength+(Encoding.vista.encode vista).length+width+
        r.size+(r+1).size+(start+1)+count+2=base := by dsimp only [base];omega
    rw [sameBase] at tail
    change _+2+levelLoopBudget vista r tableLength (start+1) count (levelChoiceWeights vista r start weights) ≤
      (count+1)*(30000*base^5+2)+1
    simp only [Nat.add_mul,Nat.one_mul]
    omega

/-- The real level loop has a uniform polynomial budget in its original
encoded array and DAG. No graph-validity or positive-weight premise occurs. -/
theorem levelLoopBudget_polynomial (vista : Executable.Vista) (r tableLength start count : Nat)
    (weights : Array Nat) (sized : weights.size=vista.nodes.size) (inside : start+count ≤ vista.nodes.size) :
    levelLoopBudget vista r tableLength start count weights ≤
      count*(30000*(tableLength+(Encoding.vista.encode vista).length+
        8*(((Encoding.array Encoding.natural).encode weights).length+1)^2+
        r.size+(r+1).size+vista.nodes.size+2)^5+2)+1 := by
  have prefixes (j : Nat) (small : j ≤ count) :
      ((Encoding.array Encoding.natural).encode (levelScan vista r start j weights)).length ≤
        8*(((Encoding.array Encoding.natural).encode weights).length+1)^2 :=
    levelScan_encoded_bound vista r start j weights sized (by omega)
  apply (levelLoopBudget_bound vista r tableLength start count weights _ prefixes).trans
  apply Nat.add_le_add_right
  apply Nat.mul_le_mul_left
  apply Nat.add_le_add_right
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 5)

end Counting.StackMachine.AuditPropagation
