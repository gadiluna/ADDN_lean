import Counting.StackRealizabilityReachTargets
import Counting.StackRealizabilityReachSpec

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem reachValues_map (arcs seen : List Bool) (width start count : Nat) :
    reachValues arcs seen width start count=(List.range count).map (fun offset=>
      reachFold arcs seen width 0 (start+offset) width (RealizabilityVerifier.BitGraph.bitAt seen (start+offset))):=by
  induction count generalizing start with
  | zero=>rfl
  | succ count ih=>
    simp only [reachValues,ih,List.range_succ_eq_map,List.map_cons,List.map_map,Nat.add_zero]
    congr 1
    apply congrArg (fun f=>(List.range count).map f)
    funext offset
    rw [show start+1+offset=start+(offset+1) by omega]
    rfl

theorem reachValues_pass (size : Nat) (arcs seen : List Bool) :
    reachValues arcs seen size 0 size=RealizabilityVerifier.BitGraph.reachPass size arcs seen:=by
  rw [reachValues_map]
  apply List.ext_getElem
  · simp
  · intro i left right
    have inside : i<size:=by simpa using left
    simp only [List.getElem_map,List.getElem_range,Nat.zero_add]
    have same:=reachFold_target size arcs seen ⟨i,inside⟩
    simpa only [RealizabilityVerifier.BitGraph.bitAt,List.getElem?_eq_getElem right,Option.getD_some] using same

/-- One synchronous pass. Registers 0, 1, and 2 retain arcs, old bits and width;
register 3 receives the new bit vector in increasing vertex order. -/
def reachPassRoutine : Routine 15:=sequence (ofProgram (ListPrograms.copyProgram 14 2 15 12))
  (sequence (forEach 15 reachTarget)
    (sequence (ofProgram (ListPrograms.reverseProgram 15 16 3)) (clear 14)))

theorem reachPass_executes (store : Store 15)
    (e3 : store 3=[]) (e4 : store 4=[]) (e5 : store 5=[]) (e6 : store 6=[]) (e7 : store 7=[])
    (e9 : store 9=[]) (e10 : store 10=[]) (e11 : store 11=[]) (e12 : store 12=[]) (e13 : store 13=[])
    (e14 : store 14=[]) (e15 : store 15=[]) (e16 : store 16=[]) :
    ∃ time ≤ 10000*((store 0).length+(store 1).length+(store 2).length+1)^4,
      Executes reachPassRoutine store time (Function.update store 3
        (RealizabilityVerifier.BitGraph.reachPass (store 2).length (store 0) (store 1))):=by
  have copying:=copy_executes 14 2 15 12 (by decide) (by decide) (by decide) store e12
  rw [e15,List.append_nil] at copying
  let prepared:=Function.update store 15 (store 2)
  obtain ⟨loopTime,loopBound,loopRun⟩:=reachTargets_executes prepared (store 2)
    (by simp [prepared])
    (by simp [prepared,e3]) (by simp [prepared,e4]) (by simp [prepared,e5])
    (by simp [prepared,e6]) (by simp [prepared,e7]) (by simp [prepared,e9])
    (by simp [prepared,e10]) (by simp [prepared,e11]) (by simp [prepared,e12]) (by simp [prepared,e13])
  let scanned:=reachTargetsStore prepared (store 2)
  have reversing:=reverse_executes 15 16 3 (by decide) scanned
  have outputAt : scanned 16=(RealizabilityVerifier.BitGraph.reachPass (store 2).length (store 0) (store 1)).reverse:=by
    simp [scanned,reachTargetsStore,prepared,e14,e16,reachValues_pass]
  have emptyAt : scanned 3=[]:=by simp [scanned,reachTargetsStore,prepared,e3]
  rw [outputAt,emptyAt,List.append_nil,List.reverse_reverse,List.length_reverse,
    RealizabilityVerifier.BitGraph.reachPass_length] at reversing
  let reversed:=Function.update (Function.update scanned 16 []) 3
    (RealizabilityVerifier.BitGraph.reachPass (store 2).length (store 0) (store 1))
  have cleaning:=clear_executes (14:Fin 17) reversed
  have targetAt : reversed 14=List.replicate (store 2).length true:=by
    simp [reversed,scanned,reachTargetsStore,prepared,e14]
  rw [targetAt,List.length_replicate] at cleaning
  have final : Function.update reversed 14 []=Function.update store 3
      (RealizabilityVerifier.BitGraph.reachPass (store 2).length (store 0) (store 1)):=by
    funext r
    fin_cases r <;> simp [reversed,scanned,reachTargetsStore,prepared,e14,e15,e16]
  rw [final] at cleaning
  have loopLimit : loopTime ≤ (store 2).length*(1000*
      ((store 0).length+(store 1).length+2*(store 2).length+1)^3+2)+1:=by
    simpa [prepared,e14,Nat.mul_two,Nat.two_mul,Nat.add_assoc] using loopBound
  let S:=(store 0).length+(store 1).length+(store 2).length+1
  have positive : 1 ≤ S:=by dsimp only [S];omega
  have width : (store 2).length ≤ S:=by dsimp only [S];omega
  have base : (store 0).length+(store 1).length+2*(store 2).length+1 ≤ 2*S:=by dsimp only [S];omega
  have loopLimit' : loopTime ≤ 8000*S^4+2*S+1:=by
    have b : loopTime ≤ S*(1000*(2*S)^3+2)+1:=by
      apply loopLimit.trans
      exact Nat.add_le_add_right (Nat.mul_le_mul width
        (Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left base 3)) 2)) 1
    have expansion (x : Nat) : x*(1000*(2*x)^3+2)+1=8000*x^4+2*x+1:=by ring
    exact expansion S ▸ b
  have linear : S ≤ S^4:=Nat.le_self_pow (by decide) _
  have one : 1 ≤ S^4:=Nat.one_le_pow _ _ positive
  exact ⟨_,by change _ ≤ 10000*S^4;dsimp only [S] at loopLimit' linear one ⊢;omega,
    copying.sequence (loopRun.sequence (reversing.sequence cleaning))⟩

end Counting.StackMachine.RealizabilityCheck
