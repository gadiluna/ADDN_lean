import Counting.StackAuditPrefixCountAll
import Counting.StackDagEmptyGuard
import Counting.StackEncodingGuards

namespace Counting.StackMachine.AuditPrefix
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

abbrev countPositive (mode : HeaderMode) : Routine 34 := sequence (countAll mode)
  (sequence (DagValidation.emptyFlag 29 35)
    (sequence (negateFlag 34 35) (clear 29)))

/-- Test whether the actual finite scan found any matching node, clearing
its unary tally and preserving the table, queries and all external data. -/
theorem countPositive_executes (mode : HeaderMode) (vista : Executable.Vista)
    (store : Store 34) (accepted : Bool) (tail : List Bool) (status : store 1=accepted::tail)
    (work : ∀ r : Fin 36,r.val<17 → r≠1 → store r=[])
    (e18 : store 18=[]) (e19 : store 19=[]) (e28 : store 28=[]) (e29 : store 29=[])
    (e31 : store 31=[]) (e33 : store 33=[]) (e34 : store 34=[]) (e35 : store 35=[])
    (suffix : List Bool) (input : store 17=Encoding.sequence Encoding.node vista.nodes.toList++suffix)
    (nodeCount : store 20=List.replicate vista.nodes.size true)
    (level parent : Nat) (levelAt : store 30=level.bits) (parentAt : store 32=parent.bits) :
    ∃ time ≤ 20010*((store 17).length+level.size+parent.size+1)^5,
      Executes (countPositive mode) store time (Function.update store 35
        [decide (0<countRange vista mode level parent 0 vista.nodes.size)]) := by
  obtain ⟨time,bound,a⟩:=countAll_executes mode vista store accepted tail status work
    e18 e19 e28 e31 e33 e34 e35 suffix input nodeCount level parent levelAt parentAt
  rw [e29,List.append_nil] at a
  let amount:=countRange vista mode level parent 0 vista.nodes.size
  let counted:=Function.update store 29 (List.replicate amount true)
  have b:=DagValidation.emptyFlag_executes (29:Fin 36) 35 counted
  have tallyAt : counted 29=List.replicate amount true := by simp [counted]
  have flagAt : counted 35=[] := by simp [counted,e35]
  rw [tallyAt,flagAt] at b
  have empty : (List.replicate amount true=[]) ↔ amount=0 := by simp
  simp only [empty] at b
  let checked:=Function.update counted 35 [decide (amount=0)]
  have c:=negateFlag_executes 34 (35:Fin 36) checked (decide (amount=0)) [] (by simp [checked])
  have positive : (!decide (amount=0))=decide (0<amount) := by simp [Nat.pos_iff_ne_zero]
  rw [positive] at c
  let decided:=Function.update counted 35 [decide (0<amount)]
  have cResult : Function.update checked 35 [decide (0<amount)]=decided := by
    simp [checked,decided]
  rw [cResult] at c
  have d:=clear_executes (29:Fin 36) decided
  have sourceAt : (decided 29).length=amount := by simp [decided,counted]
  rw [sourceAt] at d
  have final : Function.update decided 29 []=Function.update store 35 [decide (0<amount)] := by
    funext r
    by_cases r29 : r=29
    · subst r;simp [e29]
    · by_cases r35 : r=35
      · subst r;simp [decided]
      · simp [decided,counted,r29,r35]
  rw [final] at d
  refine ⟨_,?_,a.sequence (b.sequence (c.sequence d))⟩
  have emptyCost : DagValidation.emptyFlagCost (List.replicate amount true) ≤ 3 := by
    unfold DagValidation.emptyFlagCost
    split <;> omega
  have matched : amount ≤ vista.nodes.size := countRange_le vista mode level parent 0 vista.nodes.size
  have nodes:=DagValidation.node_sequence_count_le vista.nodes.toList
  have nodeBound : vista.nodes.size ≤ (store 17).length := by
    rw [input,List.length_append]
    simp only [Array.length_toList] at nodes
    omega
  let S:=(store 17).length+level.size+parent.size+1
  have linear : S ≤ S^5 := Nat.le_self_pow (by decide) _
  have one : 1 ≤ S^5 := Nat.one_le_pow _ _ (by dsimp only [S];omega)
  change time+1+(DagValidation.emptyFlagCost (List.replicate amount true)+1+(2+1+(amount+1))) ≤ 20010*S^5
  dsimp only [S] at linear one ⊢
  omega

end Counting.StackMachine.AuditPrefix
