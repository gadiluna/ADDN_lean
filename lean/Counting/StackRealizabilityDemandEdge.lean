import Counting.StackRealizabilityDemandFields

namespace Counting.StackMachine.RealizabilityCheck
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def demandEdge : Routine 30:=sequence (ofProgram (unframeProgram 29 19 2 4))
  (sequence (ofProgram (unframeProgram 29 19 27 4))
    (sequence demandFieldsSum (sequence (clear 2) (clear 27))))

def demandEdgeStore (store : Store 30) (level target source old value count total : Nat)
    (suffix : List Bool) : Store 30:=
  Function.update (Function.update store 19 suffix)
    26 (total+demandContribution level target source old value count).bits

theorem demandEdge_executes (store : Store 30) (level target source old value count total : Nat)
    (levelInput : store 0=level.bits) (targetInput : store 22=target.bits) (oldInput : store 25=old.bits)
    (weight : store 24=value.bits) (accumulator : store 26=total.bits)
    (work : ∀ r : Fin 32,4 ≤ r.val → r.val<17 → store r=[])
    (e2 : store 2=[]) (e27 : store 27=[]) (e28 : store 28=[]) (e29 : store 29=[])
    (suffix : List Bool)
    (input : store 19=(Encoding.product Encoding.natural Encoding.natural).encode (source,count)++suffix) :
    ∃ time ≤ 85000*((store 19).length+level.size+target.size+old.size+value.size+total.size+1)^3,
      Executes demandEdge store time (demandEdgeStore store level target source old value count total suffix):=by
  let remaining:=Encoding.natural.encode count++suffix
  have firstRun:=unframe_canonical_executes 29 19 2 4 (by decide) (by decide) (by decide)
    store source.bits remaining
    (by simpa only [remaining,Encoding.product,Encoding.natural,List.append_assoc] using input)
    (work 4 (by decide) (by decide))
  rw [e2,List.append_nil] at firstRun
  let firstStore:=Function.update (Function.update store 19 remaining) 2 source.bits
  have secondRun:=unframe_canonical_executes 29 19 27 4 (by decide) (by decide) (by decide)
    firstStore count.bits suffix (by simp [firstStore,remaining,Encoding.natural])
    (by simp [firstStore,work])
  have secondEmpty : firstStore 27=[]:=by simp [firstStore,e27]
  rw [secondEmpty,List.append_nil] at secondRun
  let ready:=Function.update (Function.update firstStore 19 suffix) 27 count.bits
  have readyWork (r : Fin 32) (lo : 4 ≤ r.val) (hi : r.val<17) : ready r=[]:=by
    have n2 : r≠2:=by intro same;subst r;norm_num at lo
    have n19 : r≠19:=by intro same;subst r;norm_num at hi
    have n27 : r≠27:=by intro same;subst r;norm_num at hi
    simp [ready,firstStore,n2,n19,n27,work r lo hi]
  obtain ⟨sumTime,sumBound,sumRun⟩:=demandFieldsSum_executes ready level target source old value count total
    (by simp [ready,firstStore,levelInput]) (by simp [ready,firstStore])
    (by simp [ready,firstStore,targetInput]) (by simp [ready,firstStore,oldInput])
    (by simp [ready,firstStore,weight]) (by simp [ready]) (by simp [ready,firstStore,accumulator])
    readyWork (by simp [ready,firstStore,e28]) (by simp [ready,firstStore,e29])
  let summed:=Function.update ready 26 (total+demandContribution level target source old value count).bits
  have clearSource:=clear_executes (2:Fin 32) summed
  have sourceAt : summed 2=source.bits:=by simp [summed,ready,firstStore]
  rw [sourceAt] at clearSource
  let noSource:=Function.update summed 2 []
  have clearCount:=clear_executes (27:Fin 32) noSource
  have countAt : noSource 27=count.bits:=by simp [noSource,summed,ready]
  rw [countAt] at clearCount
  have final : Function.update noSource 27 []=demandEdgeStore store level target source old value count total suffix:=by
    funext r
    by_cases n2 : r=2 <;> by_cases n19 : r=19 <;> by_cases n26 : r=26 <;> by_cases n27 : r=27 <;>
      simp [noSource,summed,ready,firstStore,demandEdgeStore,n2,n19,n26,n27,e2,e27]
  rw [final] at clearCount
  have sizes : source.size+count.size ≤ (store 19).length:=by
    rw [input]
    simp only [Encoding.product,List.length_append,Encoding.natural_length]
    omega
  let S:=(store 19).length+level.size+target.size+old.size+value.size+total.size+1
  have sumLimit : sumTime ≤ 84000*S^3:=by
    apply sumBound.trans
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp only [S];omega) 3)
  have linear : S ≤ S^3:=Nat.le_self_pow (by decide) _
  have one : 1 ≤ S^3:=Nat.one_le_pow _ _ (by dsimp only [S];omega)
  refine ⟨_,?_,firstRun.sequence (secondRun.sequence (sumRun.sequence (clearSource.sequence clearCount)))⟩
  simp only [Encoding.bits_length]
  change _ ≤ 85000*S^3
  dsimp only [S] at sumLimit linear one ⊢
  omega

end Counting.StackMachine.RealizabilityCheck
