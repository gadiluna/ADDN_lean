import Counting.StackAuditDescendantAll
import Counting.StackRoutineUnary
import Counting.StackBinaryComparePreserving

namespace Counting.StackMachine.AuditDescendant
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def countCompareRoles : Fin 6 ↪ Fin 40 := ⟨![37,31,35,0,1,2],by decide⟩

def countCompare : Routine 38 := sequence countAll
  (sequence (ofProgram (Unary.toBinaryProgram 37 39 37 0))
    (sequence (Binary.preservingComparison 34 countCompareRoles) (clear 37)))

/-- The table-sized descendant count is converted to binary and compared
against an arbitrary binary weight. No unary expansion of the weight is used. -/
theorem countCompare_executes (store : Store 38) (vista : Executable.Vista)
    (last ancestor weight : Nat) (steps bits : List Bool)
    (count : bits.length=vista.nodes.size)
    (source : store 17=Encoding.sequence Encoding.node vista.nodes.toList)
    (lastAt : store 34=last.bits) (target : store 29=(ancestor+1).bits)
    (weightAt : store 31=weight.bits)
    (stepBudget : store 38=steps) (counter : store 30=bits)
    (e35 : store 35=[]) (e36 : store 36=[]) (e37 : store 37=[]) (e39 : store 39=[])
    (empty : ∀ r : Fin 40,r.val ≤ 28 → r≠17 → store r=[]) :
    ∃ time ≤ 17000000000*((store 17).length+steps.length+(ancestor+1).size+last.size+weight.size+1)^6,
      Executes countCompare store time
        (Function.update (Function.update store 30 []) 35
          [decide (Executable.descendantCountRange vista steps.length last ancestor 0 vista.nodes.size ≤ weight)]) := by
  obtain ⟨countTime,countBound,a⟩:=countAll_executes store vista last ancestor steps bits count
    source lastAt target stepBudget counter e35 e36 e37 empty
  rw [e39,List.append_nil] at a
  let amount:=Executable.descendantCountRange vista steps.length last ancestor 0 vista.nodes.size
  let scanned:=Function.update store 30 []
  let counted:=Function.update scanned 39 (List.replicate amount true)
  obtain ⟨binaryTime,binaryBound,b⟩:=toBinary_executes 37 (39:Fin 40) 37 0
    (by decide) (by decide) (by decide) counted 0
    (by simp [counted,scanned,e37]) (by simp [counted,scanned,empty])
  have unaryLength : (counted 39).length=amount := by simp [counted]
  rw [unaryLength,Nat.zero_add] at b
  rw [unaryLength] at binaryBound
  let converted:=Function.update scanned 37 amount.bits
  have binaryStore : Function.update (Function.update counted 39 []) 37 amount.bits=converted := by
    simp only [counted,Function.update_idem]
    have initialEmpty : scanned 39=[] := by simp [scanned,e39]
    rw [←initialEmpty,Function.update_eq_self]
  rw [binaryStore] at b
  have c:=Binary.preservingComparison_executes 34 countCompareRoles converted
    (by simp [converted,scanned,countCompareRoles,empty])
    (by simp [converted,scanned,countCompareRoles,empty])
    (by simp [converted,scanned,countCompareRoles,empty])
  have left : converted (countCompareRoles 0)=amount.bits := by simp [converted,countCompareRoles]
  have right : converted (countCompareRoles 1)=weight.bits := by simp [converted,scanned,countCompareRoles,weightAt]
  have flag : converted (countCompareRoles 2)=[] := by simp [converted,scanned,countCompareRoles,e35]
  rw [left,right,flag] at c
  have comparison : Binary.compareBits true amount.bits weight.bits=decide (amount ≤ weight) := by
    apply Bool.eq_iff_iff.mpr
    simp [Binary.compareBits_le,Encoding.value_bits]
  rw [comparison] at c
  let compared:=Function.update converted 35 [decide (amount ≤ weight)]
  have d:=clear_executes (37:Fin 40) compared
  have current : compared 37=amount.bits := by simp [compared,converted]
  rw [current,Encoding.bits_length] at d
  have final : Function.update compared 37 []=Function.update scanned 35 [decide (amount ≤ weight)] := by
    funext r
    by_cases r37:r=37
    · subst r;simp [scanned,e37]
    · by_cases r35:r=35
      · subst r;simp [compared]
      · simp [compared,converted,r37,r35]
  rw [final] at d
  refine ⟨_,?_,a.sequence (b.sequence (c.sequence d))⟩
  have amountBound : amount ≤ vista.nodes.size:=Executable.descendantCountRange_le vista steps.length last ancestor 0 vista.nodes.size
  have widthBound : amount.size ≤ amount:=Nat.size_le.mpr Nat.lt_two_pow_self
  have nodes:=DagValidation.node_sequence_count_le vista.nodes.toList
  rw [Array.length_toList,←source] at nodes
  let K:=(store 17).length+steps.length+(ancestor+1).size+last.size+weight.size+1
  have positive : 1 ≤ K := by dsimp only [K];omega
  have countLimit : countTime ≤ 16000000000*K^6 := countBound.trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp only [K];omega) 6))
  have amountSize : amount ≤ K := by dsimp only [K];omega
  have binaryLimit : binaryTime ≤ 8*K^2+1 := by
    have product:=Nat.mul_le_mul amountSize (show 0+amount+1 ≤ 2*K by omega)
    have expansion : 4*(K*(2*K))=8*K^2 := by ring
    nlinarith only [binaryBound,product,expansion]
  have comparisonBound:=Binary.preservingCompareCost_le amount.bits weight.bits
  simp only [Encoding.bits_length] at comparisonBound
  have square : K^2 ≤ K^6:=Nat.pow_le_pow_right positive (by decide)
  have linear : K ≤ K^6:=Nat.le_self_pow (by decide) _
  have one : 1 ≤ K^6:=Nat.one_le_pow _ _ positive
  change countTime+1+(binaryTime+1+(Binary.preservingCompareCost amount.bits weight.bits+1+(amount.size+1))) ≤ 17000000000*K^6
  dsimp only [K] at countLimit binaryLimit square linear one ⊢
  omega

end Counting.StackMachine.AuditDescendant
