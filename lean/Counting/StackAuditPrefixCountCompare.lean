import Counting.StackAuditPrefixCountAll
import Counting.StackRoutineUnary
import Counting.StackBinaryComparePreserving

namespace Counting.StackMachine.AuditPrefix
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

def countCompareRoles : Fin 6 ↪ Fin 36 := ⟨![24,21,35,4,5,6],by decide⟩

abbrev countCompare (mode : HeaderMode) : Routine 34 := sequence (countAll mode)
  (sequence (ofProgram (Unary.toBinaryProgram 33 29 24 4))
    (sequence (Binary.preservingComparison 30 countCompareRoles) (clear 24)))

/-- Count actual selected nodes and compare the result to a binary bound.
Only the table-sized count is converted to unary and then back to binary;
the potentially large candidate remains a preserved binary payload. -/
theorem countCompare_executes (mode : HeaderMode) (vista : Executable.Vista)
    (store : Store 34) (accepted : Bool) (tail : List Bool) (status : store 1=accepted::tail)
    (work : ∀ r : Fin 36,r.val<17 → r≠1 → store r=[])
    (e18 : store 18=[]) (e19 : store 19=[]) (e24 : store 24=[]) (e28 : store 28=[]) (e29 : store 29=[])
    (e31 : store 31=[]) (e33 : store 33=[]) (e34 : store 34=[]) (e35 : store 35=[])
    (suffix : List Bool) (input : store 17=Encoding.sequence Encoding.node vista.nodes.toList++suffix)
    (nodeCount : store 20=List.replicate vista.nodes.size true)
    (level parent candidate : Nat) (levelAt : store 30=level.bits) (parentAt : store 32=parent.bits)
    (candidateAt : store 21=candidate.bits) :
    ∃ time ≤ 30000*((store 17).length+level.size+parent.size+candidate.size+1)^5,
      Executes (countCompare mode) store time (Function.update store 35
        [decide (countRange vista mode level parent 0 vista.nodes.size≤candidate)]) := by
  obtain ⟨countTime,countBound,a⟩:=countAll_executes mode vista store accepted tail status work
    e18 e19 e28 e31 e33 e34 e35 suffix input nodeCount level parent levelAt parentAt
  rw [e29,List.append_nil] at a
  let amount:=countRange vista mode level parent 0 vista.nodes.size
  let counted:=Function.update store 29 (List.replicate amount true)
  obtain ⟨binaryTime,binaryBound,b⟩:=toBinary_executes 33 (29:Fin 36) 24 4
    (by decide) (by decide) (by decide) counted 0
    (by simp [counted,e24]) (by simp [counted,work])
  have unaryLength : (counted 29).length=amount := by simp [counted]
  rw [unaryLength,Nat.zero_add] at b
  rw [unaryLength] at binaryBound
  let converted:=Function.update store 24 amount.bits
  have convertedStore : Function.update (Function.update counted 29 []) 24 amount.bits=converted := by
    simp only [counted,Function.update_idem]
    rw [←e29,Function.update_eq_self]
  rw [convertedStore] at b
  have c:=Binary.preservingComparison_executes 30 countCompareRoles converted
    (by simp [converted,countCompareRoles,work])
    (by simp [converted,countCompareRoles,work])
    (by simp [converted,countCompareRoles,work])
  have left : converted (countCompareRoles 0)=amount.bits := by simp [converted,countCompareRoles]
  have right : converted (countCompareRoles 1)=candidate.bits := by simp [converted,countCompareRoles,candidateAt]
  have flag : converted (countCompareRoles 2)=[] := by simp [converted,countCompareRoles,e35]
  rw [left,right,flag] at c
  have comparison : Binary.compareBits true amount.bits candidate.bits=decide (amount≤candidate) := by
    apply Bool.eq_iff_iff.mpr
    simp [Binary.compareBits_le,Encoding.value_bits]
  rw [comparison] at c
  let checked:=Function.update converted 35 [decide (amount≤candidate)]
  have d:=clear_executes (24:Fin 36) checked
  have current : checked 24=amount.bits := by simp [checked,converted]
  rw [current,Encoding.bits_length] at d
  have final : Function.update checked 24 []=Function.update store 35 [decide (amount≤candidate)] := by
    funext r
    by_cases r24 : r=24
    · subst r;simp [e24]
    · by_cases r35 : r=35
      · subst r;simp [checked]
      · simp [checked,converted,r24,r35]
  rw [final] at d
  refine ⟨_,?_,a.sequence (b.sequence (c.sequence d))⟩
  have amountBound : amount ≤ vista.nodes.size := countRange_le vista mode level parent 0 vista.nodes.size
  have widthBound : amount.size ≤ amount := Nat.size_le.mpr Nat.lt_two_pow_self
  have nodeLength:=DagValidation.node_sequence_count_le vista.nodes.toList
  have nodesBound : vista.nodes.size ≤ (store 17).length := by
    rw [input,List.length_append]
    simp only [Array.length_toList] at nodeLength
    omega
  have compareBound:=Binary.preservingCompareCost_le amount.bits candidate.bits
  simp only [Encoding.bits_length] at compareBound
  let S:=(store 17).length+level.size+parent.size+candidate.size+1
  have positive : 1 ≤ S := by dsimp only [S];omega
  have countLimit : countTime ≤ 20000*S^5 := countBound.trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp only [S];omega) 5))
  have amountSize : amount ≤ S := by dsimp only [S];omega
  have binaryLimit : binaryTime ≤ 8*S^2+1 := by
    have product:=Nat.mul_le_mul amountSize (show 0+amount+1 ≤ 2*S by omega)
    have expansion : 4*(S*(2*S))=8*S^2 := by ring
    nlinarith only [binaryBound,product,expansion]
  have square : S^2 ≤ S^5 := Nat.pow_le_pow_right positive (by decide)
  have linear : S ≤ S^5 := Nat.le_self_pow (by decide) _
  have one : 1 ≤ S^5 := Nat.one_le_pow _ _ positive
  change countTime+1+(binaryTime+1+(Binary.preservingCompareCost amount.bits candidate.bits+1+(amount.size+1)))
    ≤ 30000*S^5
  dsimp only [S] at countLimit binaryLimit square linear one ⊢
  omega

end Counting.StackMachine.AuditPrefix
