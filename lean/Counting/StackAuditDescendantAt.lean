import Counting.StackAuditAscendBounds
import Counting.StackComparePreserving

namespace Counting.StackMachine.AuditAscend
open Routine
set_option backward.isDefEq.respectTransparency false

theorem indexCode_injective : Function.Injective indexCode := by
  intro left right same
  cases left <;> cases right <;> simp [indexCode] at same ⊢
  exact same

theorem indexCode_bits_injective : Function.Injective (fun reference=>(indexCode reference).bits) := by
  intro left right same
  apply indexCode_injective
  have value:=congrArg Encoding.value same
  simpa only [Encoding.value_bits] using value

def ancestorEqualityRoles : Fin 6 ↪ Fin 32 := ⟨![24,29,30,0,1,2],by decide⟩

/-- Consume the explicit ascent budget, test the resulting optional
reference against the preserved target and clear the temporary reference. -/
def ancestorEquals : Routine 30 := sequence ascendLoop
  (sequence (Compare.preservingEquality 26 ancestorEqualityRoles) (clear 24))

theorem ancestorEquals_executes (store : Store 30) (vista : Executable.Vista)
    (reference target : Option Nat)
    (source : store 17=Encoding.sequence Encoding.node vista.nodes.toList)
    (current : store 24=(indexCode reference).bits)
    (targetAt : store 29=(indexCode target).bits)
    (empty : ∀ r : Fin 32,r.val ≤ 28 → r≠17 → r≠24 → r≠25 → store r=[])
    (bits : List Bool) (counter : store 25=bits) :
    ∃ time  ≤  200000000*((store 17).length+(indexCode reference).size+
        bits.length+(indexCode target).size+1)^5,
      Executes ancestorEquals store time
        (Function.update (Function.update (Function.update store 25 []) 24 []) 30
          (decide (reference.bind (Executable.ascend vista bits.length)=target)::store 30)) := by
  let result:=reference.bind (Executable.ascend vista bits.length)
  let ascended:=Function.update (Function.update store 25 []) 24 (indexCode result).bits
  obtain ⟨ascentTime,ascentBound,a⟩:=ascendLoop_ascend store vista reference source current empty bits counter
  have b:=Compare.preservingEquality_executes 26 ancestorEqualityRoles ascended
    (by simp [ascended,ancestorEqualityRoles,empty])
    (by simp [ascended,ancestorEqualityRoles,empty])
    (by simp [ascended,ancestorEqualityRoles,empty])
  have same : (indexCode result).bits=(indexCode target).bits ↔ result=target :=
    indexCode_bits_injective.eq_iff
  change Executes (Compare.preservingEquality 26 ancestorEqualityRoles) ascended
    (Compare.preservingCost (ascended 24) (ascended 29))
    (Function.update ascended 30 (decide (ascended 24=ascended 29)::ascended 30)) at b
  have leftAt : ascended 24=(indexCode result).bits := by simp [ascended]
  have rightAt : ascended 29=(indexCode target).bits := by simp [ascended,targetAt]
  have outputAt : ascended 30=store 30 := by simp [ascended]
  simp only [leftAt,rightAt,outputAt,same] at b
  let compared:=Function.update ascended 30 (decide (result=target)::store 30)
  have c:=clear_executes (24:Fin 32) compared
  have currentLength : (compared 24).length=(indexCode result).size := by
    simp [compared,ascended,Encoding.bits_length]
  rw [currentLength] at c
  have final : Function.update compared 24 []=
      Function.update (Function.update (Function.update store 25 []) 24 []) 30
        (decide (result=target)::store 30) := by
    funext r
    by_cases currentReg : r=24
    · subst r;simp [compared,ascended]
    · by_cases outputReg : r=30
      · subst r;simp [compared,ascended]
      · simp [compared,ascended,currentReg,outputReg]
  rw [final] at c
  refine ⟨_,?_,a.sequence (b.sequence c)⟩
  have width:=walkCode_size vista bits.length (indexCode reference)
  rw [walkCode_ascend,←source] at width
  change (indexCode result).size ≤ max (indexCode reference).size (store 17).length at width
  have comparison:=Compare.preservingCost_le (indexCode result).bits (indexCode target).bits
  simp only [Encoding.bits_length] at comparison
  let K:=(store 17).length+(indexCode reference).size+bits.length+(indexCode target).size+1
  have positive : 1 ≤ K := by dsimp only [K];omega
  have codeWidth : (indexCode result).size ≤ K := by dsimp only [K];omega
  have targetWidth : (indexCode target).size ≤ K := by dsimp only [K];omega
  have ascentPower:=Nat.pow_le_pow_left
    (show (store 17).length+(indexCode reference).size+bits.length+1 ≤ K by dsimp only [K];omega) 5
  have linear : K ≤ K^5 := Nat.le_self_pow (by decide) _
  have one : 1 ≤ K^5 := Nat.one_le_pow _ _ positive
  change ascentTime+1+(Compare.preservingCost (indexCode result).bits (indexCode target).bits+
    1+((indexCode result).size+1)) ≤ 200000000*K^5
  nlinarith only [ascentBound,ascentPower,comparison,codeWidth,targetWidth,linear,one]

end Counting.StackMachine.AuditAscend
