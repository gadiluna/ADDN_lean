import Counting.StackRealizabilityReachLoop

namespace Counting.StackMachine.RealizabilityCheck

theorem reachFold_eq_any (arcs seen : List Bool) (width source arc count : Nat) (value : Bool) :
    reachFold arcs seen width source arc count value=
      (value || (List.range count).any (fun offset=>
        RealizabilityVerifier.BitGraph.bitAt seen (source+offset) &&
          RealizabilityVerifier.BitGraph.bitAt arcs (arc+offset*width))):=by
  induction count generalizing source arc value with
  | zero=>simp [reachFold]
  | succ count ih=>
    rw [reachFold,ih]
    simp only [List.range_succ_eq_map,List.any_cons,List.any_map,Nat.add_zero,Nat.zero_mul,
      Bool.or_assoc]
    apply congrArg (fun bit=>value || ((RealizabilityVerifier.BitGraph.bitAt seen source &&
      RealizabilityVerifier.BitGraph.bitAt arcs arc)||bit))
    apply congrArg (fun f=> (List.range count).any f)
    funext offset
    rw [show source+1+offset=source+(offset+1) by omega,
      show arc+width+offset*width=arc+(offset+1)*width by ring]
    rfl

theorem reachFold_target (size : Nat) (arcs seen : List Bool) (target : Fin size) :
    reachFold arcs seen size 0 target.val size (RealizabilityVerifier.BitGraph.bitAt seen target.val)=
      RealizabilityVerifier.BitGraph.bitAt (RealizabilityVerifier.BitGraph.reachPass size arcs seen) target.val:=by
  rw [reachFold_eq_any,RealizabilityVerifier.BitGraph.reachPass_at]
  apply congrArg (fun bit=>RealizabilityVerifier.BitGraph.bitAt seen target.val || bit)
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true,List.mem_range,List.mem_finRange,true_and,Nat.zero_add]
  constructor
  · rintro ⟨index,inside,found⟩
    exact ⟨⟨index,inside⟩,by simpa only [RealizabilityVerifier.BitGraph.edge,Nat.add_comm] using found⟩
  · rintro ⟨source,found⟩
    exact ⟨source.val,source.isLt,by simpa only [RealizabilityVerifier.BitGraph.edge,Nat.add_comm] using found⟩

end Counting.StackMachine.RealizabilityCheck
