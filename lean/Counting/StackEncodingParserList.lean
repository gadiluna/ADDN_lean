import Counting.StackEncodingParserListPrepare
import Counting.StackEncodingParserListEffect

namespace Counting.StackMachine.EncodingPrograms

set_option backward.isDefEq.respectTransparency false

/-- General list composition. A nested parser may reuse temporary stacks,
but must preserve the enclosing list's live unary counter. -/
def listParser (extra : Nat) (w : FullListWorkspace extra)
    {α : Type} {codec : Encoding.Codec α}
    (item : VerifiedParser (extra+15) (w 0) (w 1) (w 6) α codec)
    (unused : w 4∉item.work) (positive : ∀ value,0<(codec.encode value).length) :
    VerifiedParser (extra+15) (w 0) (w 1) (w 6) (List α) (Encoding.list codec) where
  work := listHeaderWork extra w ∪ item.work
  separate r member := by
    rcases Finset.mem_union.mp member with header | child
    · simp only [listHeaderWork,Finset.mem_insert,Finset.mem_singleton] at header
      rcases header with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp [w.injective.eq_iff]
    · exact item.separate r child
  routine := Routine.sequence (listPrepare extra w) (Routine.forEach (w 4) item.routine)
  effect := listEffect item.effect
  coefficient := 1820+item.coefficient
  exponent := max 3 (item.exponent+1)
  suffix_le := item.list_effect_suffix
  code_le input := by
    apply (item.list_effect_code_bound input).trans
    unfold Complexity.polynomial
    apply Nat.mul_le_mul
    · omega
    · exact Nat.pow_le_pow_right (by omega) (le_max_right _ _)
  sound := item.list_effect_sound
  roundtrip := item.list_effect_roundtrip positive
  executes store accepted tail statusEq workEmpty := by
    have ne (i j : Fin 17) (h : i≠j) : w i≠w j := fun eq => h (w.injective eq)
    have headerEmpty r member : store r=[] := workEmpty r (Finset.mem_union_left _ member)
    obtain ⟨prepareTime,prepareBound,prepareRun⟩:=listPrepare_executes extra w store accepted tail statusEq headerEmpty
    let input:=store (w 0)
    let headerStore:=parseStore (w 0) (w 1) (w 6) store accepted tail (headerEffect input)
    let prepared:=Function.update headerStore (w 4) (List.replicate (listCount input) true)
    have nextSource : prepared (w 0)=unframeSuffix input := by
      simp [prepared,headerStore,parseStore,headerEffect,w.injective.eq_iff]
    have nextStatus : prepared (w 1)=(accepted && listHeaderAccepted input)::tail := by
      simp [prepared,headerStore,parseStore,headerEffect,w.injective.eq_iff]
    have nextCounter : prepared (w 4)=List.replicate (listCount input) true := by simp [prepared]
    have nextEmpty (r : Fin (extra+17)) (member : r∈item.work) : prepared r=[] := by
      obtain ⟨rs,rt,ro⟩:=item.separate r member
      have rc : r≠w 4 := fun same => unused (same ▸ member)
      simp only [prepared,Function.update_of_ne rc,headerStore,parseStore,if_neg rs,if_neg rt,if_neg ro]
      exact workEmpty r (Finset.mem_union_right _ member)
    have nextBound : (prepared (w 0)).length≤ input.length := by rw [nextSource]; exact unframe_suffix_length input
    obtain ⟨loopTime,loopBound,loopRun⟩:=item.loop_executes
      (ne 0 1 (by decide)) (ne 0 6 (by decide)) (ne 1 6 (by decide))
      (w 4) (ne 4 0 (by decide)) (ne 4 1 (by decide)) (ne 4 6 (by decide)) unused
      (List.replicate (listCount input) true) prepared (accepted && listHeaderAccepted input) tail
      nextStatus nextEmpty nextCounter input.length nextBound
    have counterEmpty : store (w 4)=[] := headerEmpty _ (by simp [listHeaderWork])
    have restoredCounter : Function.update prepared (w 4) []=headerStore := by
      simp only [prepared,Function.update_idem]
      have initial : headerStore (w 4)=[] := by simp [headerStore,parseStore,w.injective.eq_iff,counterEmpty]
      rw [←initial,Function.update_eq_self]
    rw [nextSource,restoredCounter,List.length_replicate] at loopRun
    have combined :
        parseStore (w 0) (w 1) (w 6) headerStore (accepted && listHeaderAccepted input) tail
          (manyEffect item.effect (listCount input) (unframeSuffix input))=
        parseStore (w 0) (w 1) (w 6) store accepted tail (listEffect item.effect input) := by
      change parseStore (w 0) (w 1) (w 6)
        (parseStore (w 0) (w 1) (w 6) store accepted tail (headerEffect input))
        (accepted && (headerEffect input).accepted) tail _=_
      rw [parseStore_product (w 0) (w 1) (w 6) (ne 0 1 (by decide)) (ne 0 6 (by decide)) (ne 1 6 (by decide))]
      rfl
    rw [combined] at loopRun
    refine ⟨prepareTime+1+loopTime,?_,prepareRun.sequence loopRun⟩
    simp only [List.length_replicate] at loopBound
    have countBound:=(listCount_le input).trans (unframe_suffix_length input)
    let L:=input.length+1
    let E:=max 3 (item.exponent+1)
    have cubes : L^3≤ L^E := Nat.pow_le_pow_right (by dsimp [L];omega) (le_max_left _ _)
    have powers : L^(item.exponent+1)≤ L^E := Nat.pow_le_pow_right (by dsimp [L];omega) (le_max_right _ _)
    have linear : L≤ L^E := Nat.le_self_pow (by dsimp [E];omega) L
    have body : input.length*Complexity.polynomial item.coefficient item.exponent input.length≤ item.coefficient*L^E := by
      calc
        _≤ L*(item.coefficient*L^item.exponent) := by unfold Complexity.polynomial L;gcongr;omega
        _=item.coefficient*L^(item.exponent+1) := by ring
        _≤_ := Nat.mul_le_mul_left _ powers
    change prepareTime≤1810*L^3 at prepareBound
    change _≤(1820+item.coefficient)*L^E
    have prep:=prepareBound.trans (Nat.mul_le_mul_left 1810 cubes)
    have countCost:=Nat.mul_le_mul_right (Complexity.polynomial item.coefficient item.exponent input.length+2) countBound
    change input.length+1≤L^E at linear
    nlinarith only [prep,body,loopBound,countCost,linear]

end Counting.StackMachine.EncodingPrograms
