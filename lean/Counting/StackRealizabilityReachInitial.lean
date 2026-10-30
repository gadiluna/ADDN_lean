import Counting.StackRealizabilityReachInitialLoop

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem reachInitialValues_map (source start count : Nat) :
    reachInitialValues source start count=(List.range count).map (fun offset=>decide (source=start+offset)):=by
  induction count generalizing start with
  | zero=>rfl
  | succ count ih=>
    simp only [reachInitialValues,ih,List.range_succ_eq_map,List.map_cons,List.map_map,Nat.add_zero]
    congr 1
    apply congrArg (fun f=>(List.range count).map f)
    funext offset
    rw [show start+1+offset=start+(offset+1) by omega]
    rfl

theorem reachInitialValues_initial (width : Nat) (source : Fin width) :
    reachInitialValues source.val 0 width=RealizabilityVerifier.BitGraph.initial width source:=by
  rw [reachInitialValues_map]
  apply List.ext_getElem
  · simp [RealizabilityVerifier.BitGraph.initial]
  · intro i left right
    have inside : i<width:=by simpa using left
    simp only [List.getElem_map,List.getElem_range,Nat.zero_add]
    have same:=RealizabilityVerifier.BitGraph.initial_at width source ⟨i,inside⟩
    rw [RealizabilityVerifier.BitGraph.bitAt,List.getElem?_eq_getElem right,Option.getD_some] at same
    rw [same]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq,beq_iff_eq,Fin.ext_iff]
    omega

/-- Build a one-hot vector from explicit width/source lengths. No word value
is expanded into unary; the source itself is already a length counter. -/
def reachInitialRoutine : Routine 8:=sequence (ofProgram (ListPrograms.copyProgram 7 0 8 7))
  (sequence (forEach 8 reachInitialItem)
    (sequence (ofProgram (ListPrograms.reverseProgram 8 3 9)) (clear 2)))

theorem reachInitial_executes (store : Store 8)
    (e2 : store 2=[]) (e3 : store 3=[]) (e4 : store 4=[]) (e5 : store 5=[]) (e6 : store 6=[])
    (e7 : store 7=[]) (e8 : store 8=[]) (e9 : store 9=[]) :
    ∃ time ≤ 40*((store 0).length+(store 1).length+1)^2,
      Executes reachInitialRoutine store time
        (Function.update store 9 (reachInitialValues (store 1).length 0 (store 0).length)):=by
  have copying:=copy_executes 7 0 8 7 (by decide) (by decide) (by decide) store e7
  rw [e8,List.append_nil] at copying
  let prepared:=Function.update store 8 (store 0)
  obtain ⟨loopTime,loopBound,loopRun⟩:=reachInitialLoop_executes prepared (store 0)
    (by simp [prepared]) (by simp [prepared,e4]) (by simp [prepared,e5])
    (by simp [prepared,e6]) (by simp [prepared,e2])
  let scanned:=reachInitialLoopStore prepared (store 0)
  have reversing:=reverse_executes 8 3 9 (by decide) scanned
  have valuesAt : scanned 3=(reachInitialValues (store 1).length 0 (store 0).length).reverse:=by
    simp [scanned,reachInitialLoopStore,prepared,e2,e3]
  have outputAt : scanned 9=[]:=by simp [scanned,reachInitialLoopStore,prepared,e9]
  rw [valuesAt,outputAt,List.append_nil,List.reverse_reverse,List.length_reverse,reachInitialValues_length] at reversing
  let reversed:=Function.update (Function.update scanned 3 []) 9 (reachInitialValues (store 1).length 0 (store 0).length)
  have cleaning:=clear_executes (2:Fin 10) reversed
  have indexAt : reversed 2=List.replicate (store 0).length true:=by
    simp [reversed,scanned,reachInitialLoopStore,prepared,e2]
  rw [indexAt,List.length_replicate] at cleaning
  have final : Function.update reversed 2 []=Function.update store 9 (reachInitialValues (store 1).length 0 (store 0).length):=by
    funext r
    fin_cases r <;> simp [reversed,scanned,reachInitialLoopStore,prepared,e2,e3,e8]
  rw [final] at cleaning
  have loopLimit : loopTime ≤ (store 0).length*(6*((store 1).length+(store 0).length)+15)+1:=by
    simpa [prepared,e2] using loopBound
  let S:=(store 0).length+(store 1).length+1
  have width : (store 0).length ≤ S:=by dsimp only [S];omega
  have base : (store 1).length+(store 0).length ≤ S:=by dsimp only [S];omega
  have bound : loopTime ≤ 6*S^2+15*S+1:=by
    have b : loopTime ≤ S*(6*S+15)+1:=by
      apply loopLimit.trans
      exact Nat.add_le_add_right (Nat.mul_le_mul width (Nat.add_le_add_right (Nat.mul_le_mul_left _ base) 15)) 1
    have expansion (x : Nat) : x*(6*x+15)+1=6*x^2+15*x+1:=by ring
    exact expansion S ▸ b
  have linear : S ≤ S^2:=Nat.le_self_pow (by decide) _
  have one : 1 ≤ S^2:=Nat.one_le_pow _ _ (by dsimp only [S];omega)
  exact ⟨_,by change _ ≤ 40*S^2;dsimp only [S] at bound linear one ⊢;omega,
    copying.sequence (loopRun.sequence (reversing.sequence cleaning))⟩

end Counting.StackMachine.RealizabilityCheck
