import Counting.StackRealizabilityReachRows

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem range_all_fin (width : Nat) (predicate : Nat → Bool) :
    (List.range width).all predicate=(List.finRange width).all (fun i=>predicate i.val):=by
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true,List.mem_range,List.mem_finRange,true_implies]
  constructor
  · intro all i;exact all i.val i.isLt
  · intro all i inside;exact all ⟨i,inside⟩

theorem rowSeen_iterate (width : Nat) (arcs : List Bool) (source : Fin width) :
    rowSeen width arcs source.val=RealizabilityVerifier.BitGraph.iterate width arcs source width:=by
  unfold rowSeen
  rw [reachInitialValues_initial width source]
  simpa only [RealizabilityVerifier.BitGraph.iterate,Nat.zero_add] using
    reachIterations_iterate width arcs source 0 width

theorem checkSource_eq (width : Nat) (arcs active : List Bool) (source : Fin width) :
    checkSource width arcs active source.val=
      (!RealizabilityVerifier.BitGraph.bitAt active source.val ||
        (List.finRange width).all (fun target=>!RealizabilityVerifier.BitGraph.bitAt active target.val ||
          RealizabilityVerifier.BitGraph.bitAt (RealizabilityVerifier.BitGraph.iterate width arcs source width) target.val)):=by
  rw [checkSource,rowSeen_iterate,implicationFold_all,Bool.true_and,range_all_fin]

theorem rowsFold_all (width : Nat) (arcs active : List Bool) (start count : Nat) (value : Bool) :
    rowsFold width arcs active start count value=
      (value && (List.range count).all (fun offset=>checkSource width arcs active (start+offset))):=by
  induction count generalizing start value with
  | zero=>simp [rowsFold]
  | succ count ih=>
    rw [rowsFold,ih]
    simp only [List.range_succ_eq_map,List.all_cons,List.all_map,Nat.add_zero,Bool.and_assoc]
    apply congrArg (fun bit=>value && (checkSource width arcs active start && bit))
    apply congrArg (fun f=>(List.range count).all f)
    funext i
    rw [show start+1+i=start+(i+1) by omega]
    rfl

theorem rowsFold_check (width : Nat) (arcs active : List Bool) (value : Bool) :
    rowsFold width arcs active 0 width value=(value && RealizabilityVerifier.BitGraph.check width arcs active):=by
  rw [rowsFold_all]
  simp only [Nat.zero_add]
  rw [range_all_fin]
  apply congrArg (fun bit=>value && bit)
  apply congrArg (fun f=>(List.finRange width).all f)
  funext source
  exact checkSource_eq width arcs active source

/-- Strong connectivity on the explicit active slots of a flat Boolean
matrix. Empty/truncated masks and matrices use the same false defaults as the
specification. The input data is preserved and the accumulator is updated. -/
def reachCheckRoutine : Routine 22:=sequence (ofProgram (ListPrograms.copyProgram 21 2 23 12))
  (sequence (forEach 23 rowItem) (clear 17))

theorem reachCheck_executes (store : Store 22) (value : Bool) (tail : List Bool)
    (accumulated : store 19=value::tail) (empty : RowEmpty store) (e17 : store 17=[]) (e23 : store 23=[]) :
    ∃ time ≤ 7000000*((store 0).length+(store 18).length+(store 2).length+1)^6,
      Executes reachCheckRoutine store time (Function.update store 19
        ((value && RealizabilityVerifier.BitGraph.check (store 2).length (store 0) (store 18))::tail)):=by
  have copying:=copy_executes 21 2 23 12 (by decide) (by decide) (by decide) store
    (empty 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  rw [e23,List.append_nil] at copying
  let prepared:=Function.update store 23 (store 2)
  obtain ⟨loopTime,loopBound,loopRun⟩:=rows_executes prepared (store 2) (by simp [prepared]) value tail
    (by simp [prepared,accumulated])
    (by intro r n0 n2 n17 n18 n19 n23;simp [prepared,n23,empty r n0 n2 n17 n18 n19 n23])
  let scanned:=rowsStore prepared (store 2).length value tail
  have cleaning:=clear_executes (17:Fin 24) scanned
  have indexAt : scanned 17=List.replicate (store 2).length true:=by
    simp [scanned,rowsStore,prepared,e17]
  rw [indexAt,List.length_replicate] at cleaning
  have final : Function.update scanned 17 []=Function.update store 19
      ((value && RealizabilityVerifier.BitGraph.check (store 2).length (store 0) (store 18))::tail):=by
    funext r
    by_cases n17 : r=17 <;> by_cases n19 : r=19 <;> by_cases n23 : r=23 <;>
      simp [scanned,rowsStore,prepared,e17,e23,n17,n19,n23,rowsFold_check]
  rw [final] at cleaning
  have loopLimit : loopTime ≤ (store 2).length*(202000*
      ((store 0).length+(store 18).length+2*(store 2).length+1)^5+2)+1:=by
    simpa [prepared,e17,Nat.two_mul,Nat.add_assoc] using loopBound
  let S:=(store 0).length+(store 18).length+(store 2).length+1
  have positive : 1 ≤ S:=by dsimp only [S];omega
  have width : (store 2).length ≤ S:=by dsimp only [S];omega
  have base : (store 0).length+(store 18).length+2*(store 2).length+1 ≤ 2*S:=by dsimp only [S];omega
  have loopLimit' : loopTime ≤ 6464000*S^6+2*S+1:=by
    have b : loopTime ≤ S*(202000*(2*S)^5+2)+1:=by
      apply loopLimit.trans
      exact Nat.add_le_add_right (Nat.mul_le_mul width
        (Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left base 5)) 2)) 1
    have expansion (x : Nat) : x*(202000*(2*x)^5+2)+1=6464000*x^6+2*x+1:=by ring
    exact expansion S ▸ b
  have linear : S ≤ S^6:=Nat.le_self_pow (by decide) _
  have one : 1 ≤ S^6:=Nat.one_le_pow _ _ positive
  exact ⟨_,by change _ ≤ 7000000*S^6;dsimp only [S] at loopLimit' linear one ⊢;omega,
    copying.sequence (loopRun.sequence cleaning)⟩

end Counting.StackMachine.RealizabilityCheck
