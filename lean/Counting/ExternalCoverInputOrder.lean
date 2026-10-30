import Counting.ExternalCoverInputValidity
import Counting.StackNaturalPayloadRead
import Counting.StackRoutineFixedPrefix

namespace Counting.External.CoverInputValidation
open StackMachine StackMachine.Routine StackMachine.EncodingPrograms SATVerification
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

def orderScratch : List (Fin 32):=[2,3,4,5,18,19,20]

def orderRoles (extra : Nat) (w : SATWorkspace extra) (which : Bool) : Fin 6 ↪ Fin (extra+32) :=
  ⟨fun i=>w ((if which then ![20,19,1,3,4,5] else ![19,18,1,3,4,5]) i),by
    intro i j same
    have equal:=w.injective same
    cases which <;> fin_cases i <;> fin_cases j <;> simp_all⟩

def orderedTriple (extra : Nat) (w : SATWorkspace extra) : Routine (extra+30) :=
  sequence (discard (w 0) (Encoding.natural.encode 3).length)
    (sequence (readNaturalPayload (extra+28) (w 0) (w 18) (w 2) (w 1))
      (sequence (readNaturalPayload (extra+28) (w 0) (w 19) (w 2) (w 1))
        (sequence (readNaturalPayload (extra+28) (w 0) (w 20) (w 2) (w 1))
          (sequence (strictGuard (extra+26) (orderRoles extra w false))
            (sequence (strictGuard (extra+26) (orderRoles extra w true))
              (sequence (clear (w 18)) (sequence (clear (w 19)) (clear (w 20)))))))))

theorem not_compare_bits (a b : Nat) :
    (!Binary.compareBits true b.bits a.bits)=decide (a < b) := by
  have comparison:=Binary.compareBits_le b.bits a.bits
  simp only [Encoding.value_bits] at comparison
  cases h : Binary.compareBits true b.bits a.bits <;> simp_all

theorem orderedTriple_executes (extra : Nat) (w : SATWorkspace extra)
    (store : Fin (extra+32) → List Bool) (a b c : Nat) (accepted : Bool) (suffix tail : List Bool)
    (source : store (w 0)=(Encoding.list Encoding.natural).encode [a,b,c]++suffix)
    (status : store (w 1)=accepted::tail) (empty : ∀ i∈orderScratch,store (w i)=[]) :
    ∃ time ≤ 100*((store (w 0)).length+1),
      Executes (orderedTriple extra w) store time
        (Function.update (Function.update store (w 0) suffix)
          (w 1) ((accepted && decide (a < b ∧ b < c))::tail)) := by
  have ne (i j : Fin 32) (h : i≠j) : w i≠w j:=fun same=>h (w.injective same)
  let afterA:=Encoding.natural.encode b++Encoding.natural.encode c++suffix
  let afterB:=Encoding.natural.encode c++suffix
  let rest:=Encoding.natural.encode a++afterA
  have sourceAs : store (w 0)=Encoding.natural.encode 3++rest := by
    simpa only [Encoding.list,Encoding.sequence,List.length_cons,List.length_nil,List.append_nil,
      List.append_assoc,rest,afterA] using source
  have discarded:=discard_executes (w 0) (Encoding.natural.encode 3).length store
  simp only [sourceAs,List.drop_left] at discarded
  let prepared:=Function.update store (w 0) rest
  obtain ⟨ta,ba,ra⟩:=readNaturalPayload_executes (extra+28) (w 0) (w 18) (w 2) (w 1)
    (ne 0 18 (by decide)) (ne 0 2 (by decide)) (ne 18 2 (by decide))
    (ne 1 0 (by decide)) (ne 1 18 (by decide)) (ne 1 2 (by decide)) prepared a afterA accepted tail
    (by simp [prepared,rest]) (by simp [prepared,w.injective.eq_iff,status])
    (by simp [prepared,w.injective.eq_iff,empty,orderScratch])
    (by simp [prepared,w.injective.eq_iff,empty,orderScratch])
  let first:=Function.update (Function.update prepared (w 0) afterA) (w 18) a.bits
  obtain ⟨tb,bb,rb⟩:=readNaturalPayload_executes (extra+28) (w 0) (w 19) (w 2) (w 1)
    (ne 0 19 (by decide)) (ne 0 2 (by decide)) (ne 19 2 (by decide))
    (ne 1 0 (by decide)) (ne 1 19 (by decide)) (ne 1 2 (by decide)) first b afterB accepted tail
    (by simp [first,w.injective.eq_iff,afterA,afterB,List.append_assoc])
    (by simp [first,prepared,w.injective.eq_iff,status])
    (by simp [first,prepared,w.injective.eq_iff,empty,orderScratch])
    (by simp [first,prepared,w.injective.eq_iff,empty,orderScratch])
  let second:=Function.update (Function.update first (w 0) afterB) (w 19) b.bits
  obtain ⟨tc,bc,rc⟩:=readNaturalPayload_executes (extra+28) (w 0) (w 20) (w 2) (w 1)
    (ne 0 20 (by decide)) (ne 0 2 (by decide)) (ne 20 2 (by decide))
    (ne 1 0 (by decide)) (ne 1 20 (by decide)) (ne 1 2 (by decide)) second c suffix accepted tail
    (by simp [second,w.injective.eq_iff,afterB])
    (by simp [second,first,prepared,w.injective.eq_iff,status])
    (by simp [second,first,prepared,w.injective.eq_iff,empty,orderScratch])
    (by simp [second,first,prepared,w.injective.eq_iff,empty,orderScratch])
  let third:=Function.update (Function.update second (w 0) suffix) (w 20) c.bits
  have ab:=strictGuard_executes (extra+26) (orderRoles extra w false) third accepted tail
    (by simp [orderRoles,third,second,first,prepared,w.injective.eq_iff,status])
    (by simp [orderRoles,third,second,first,prepared,w.injective.eq_iff,empty,orderScratch])
    (by simp [orderRoles,third,second,first,prepared,w.injective.eq_iff,empty,orderScratch])
    (by simp [orderRoles,third,second,first,prepared,w.injective.eq_iff,empty,orderScratch])
  have abAs : Executes (strictGuard (extra+26) (orderRoles extra w false)) third
      (Binary.preservingCompareCost b.bits a.bits+7)
      (Function.update third (w 1) ((accepted && decide (a < b))::tail)) := by
    simpa [orderRoles,third,second,first,w.injective.eq_iff,not_compare_bits] using ab
  let firstChecked:=Function.update third (w 1) ((accepted && decide (a < b))::tail)
  have bcr:=strictGuard_executes (extra+26) (orderRoles extra w true) firstChecked
    (accepted && decide (a < b)) tail
    (by simp [orderRoles,firstChecked])
    (by simp [orderRoles,firstChecked,third,second,first,prepared,w.injective.eq_iff,empty,orderScratch])
    (by simp [orderRoles,firstChecked,third,second,first,prepared,w.injective.eq_iff,empty,orderScratch])
    (by simp [orderRoles,firstChecked,third,second,first,prepared,w.injective.eq_iff,empty,orderScratch])
  have bcrAs : Executes (strictGuard (extra+26) (orderRoles extra w true)) firstChecked
      (Binary.preservingCompareCost c.bits b.bits+7)
      (Function.update firstChecked (w 1) (((accepted && decide (a < b)) && decide (b < c))::tail)) := by
    simpa [orderRoles,firstChecked,third,second,w.injective.eq_iff,not_compare_bits] using bcr
  let checked:=Function.update firstChecked (w 1) (((accepted && decide (a < b)) && decide (b < c))::tail)
  have clearA:=clear_executes (w 18) checked
  have clearB:=clear_executes (w 19) (Function.update checked (w 18) [])
  have clearC:=clear_executes (w 20) (Function.update (Function.update checked (w 18) []) (w 19) [])
  have atA : checked (w 18)=a.bits:=by simp [checked,firstChecked,third,second,first,w.injective.eq_iff]
  have atB : Function.update checked (w 18) [] (w 19)=b.bits:=by simp [checked,firstChecked,third,second,w.injective.eq_iff]
  have atC : Function.update (Function.update checked (w 18) []) (w 19) [] (w 20)=c.bits:=by simp [checked,firstChecked,third,w.injective.eq_iff]
  rw [atA] at clearA
  rw [atB] at clearB
  rw [atC] at clearC
  have final : Function.update (Function.update (Function.update checked (w 18) []) (w 19) []) (w 20) []=
      Function.update (Function.update store (w 0) suffix) (w 1) ((accepted && decide (a < b ∧ b < c))::tail) := by
    funext r
    by_cases n20 : r=w 20
    · subst r;simp [w.injective.eq_iff,empty,orderScratch]
    · by_cases n19 : r=w 19
      · subst r;simp [w.injective.eq_iff,empty,orderScratch]
      · by_cases n18 : r=w 18
        · subst r;simp [w.injective.eq_iff,empty,orderScratch]
        · by_cases n1 : r=w 1
          · subst r;simp [checked,firstChecked,w.injective.eq_iff,Bool.and_assoc ]
          · by_cases n0 : r=w 0
            · subst r;simp [checked,firstChecked,third,second,first,w.injective.eq_iff]
            · simp [checked,firstChecked,third,second,first,prepared,n0,n1,n18,n19,n20]
  rw [final] at clearC
  have combined:=discarded.sequence (ra.sequence (rb.sequence (rc.sequence
    (abAs.sequence (bcrAs.sequence (clearA.sequence (clearB.sequence clearC)))))))
  refine ⟨_,?_,combined⟩
  have abBound:=Binary.preservingCompareCost_le b.bits a.bits
  have bcBound:=Binary.preservingCompareCost_le c.bits b.bits
  have lengths : (Encoding.natural.encode 3).length+a.bits.length+b.bits.length+c.bits.length ≤ (store (w 0)).length := by
    rw [sourceAs]
    simp only [rest,afterA,List.length_append,Encoding.natural,Encoding.frame_length]
    omega
  simp only [prepared,first,second,Function.update_self,
    Function.update_of_ne (ne 0 18 (by decide)),Function.update_of_ne (ne 0 19 (by decide))] at ba bb bc
  have suffixBounds : rest.length ≤ (store (w 0)).length ∧ afterA.length ≤ (store (w 0)).length ∧
      afterB.length ≤ (store (w 0)).length := by
    rw [sourceAs];simp only [rest,afterA,afterB,List.length_append];omega
  omega

end Counting.External.CoverInputValidation
