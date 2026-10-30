import Counting.StackRealizabilityActiveLoop
import Counting.RealizabilityCompactFields

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

theorem activeValues_map (newBits oldBits outsideBits : List Bool) (start count : Nat) :
    activeValues newBits oldBits outsideBits start count=
      (List.range count).map (fun offset=>activeBit newBits oldBits outsideBits (start+offset)):=by
  induction count generalizing start with
  | zero=>rfl
  | succ count ih=>
    simp only [activeValues,ih,List.range_succ_eq_map,List.map_cons,List.map_map,Nat.add_zero]
    congr 1
    apply congrArg (fun f=>(List.range count).map f)
    funext offset
    rw [show start+1+offset=start+(offset+1) by omega]
    rfl

theorem activeValues_fields (size : Nat) (newBits oldBits outsideBits degreeBits leavingBits
    deficitBits parentBits incomingBits : List Bool) :
    activeValues newBits oldBits outsideBits 0 size=
      RealizabilityVerifier.CompactGraph.vectorBits (RealizabilityVerifier.CompactGraph.fieldsActive
        (RealizabilityVerifier.CompactGraph.fieldsFromBits size newBits oldBits outsideBits
          degreeBits leavingBits deficitBits parentBits incomingBits)):=by
  rw [activeValues_map]
  apply List.ext_getElem
  · simp
  · intro i left right
    have inside : i<size:=by simpa using left
    simp only [List.getElem_map,List.getElem_range,Nat.zero_add,
      RealizabilityVerifier.CompactGraph.vectorBits,List.getElem_ofFn]
    rfl

/-- Construct the entire active-vertex vector by scanning the explicit width.
The three masks and width are preserved; scratch is restored and output is in
increasing slot order. Truncated masks retain the false lookup convention. -/
def activeVector : Routine 12:=sequence (ofProgram (ListPrograms.copyProgram 11 4 13 10))
  (sequence (forEach 13 activeItem)
    (sequence (ofProgram (ListPrograms.reverseProgram 12 8 5)) (clear 3)))

theorem activeVector_executes (store : Store 12)
    (e3 : store 3=[]) (e5 : store 5=[]) (e6 : store 6=[]) (e7 : store 7=[]) (e8 : store 8=[])
    (e10 : store 10=[]) (e11 : store 11=[]) (e12 : store 12=[]) (e13 : store 13=[]) :
    ∃ time ≤ 1000*((store 0).length+(store 1).length+(store 2).length+(store 4).length+1)^2,
      Executes activeVector store time (Function.update store 5
        (activeValues (store 0) (store 1) (store 2) 0 (store 4).length)):=by
  have copying:=copy_executes 11 4 13 10 (by decide) (by decide) (by decide) store e10
  rw [e13,List.append_nil] at copying
  let prepared:=Function.update store 13 (store 4)
  obtain ⟨loopTime,loopBound,loopRun⟩:=activeLoop_executes prepared (store 4) (by simp [prepared])
    (by simp [prepared,e5]) (by simp [prepared,e6]) (by simp [prepared,e7])
    (by simp [prepared,e10]) (by simp [prepared,e11]) (by simp [prepared,e12])
  let scanned:=activeLoopStore prepared (store 4)
  have reversing:=reverse_executes 12 8 5 (by decide) scanned
  have outputAt : scanned 8=(activeValues (store 0) (store 1) (store 2) 0 (store 4).length).reverse:=by
    simp [scanned,activeLoopStore,prepared,e3,e8]
  have emptyAt : scanned 5=[]:=by simp [scanned,activeLoopStore,prepared,e5]
  rw [outputAt,emptyAt,List.append_nil,List.reverse_reverse,List.length_reverse,activeValues_length] at reversing
  let reversed:=Function.update (Function.update scanned 8 []) 5
    (activeValues (store 0) (store 1) (store 2) 0 (store 4).length)
  have cleaning:=clear_executes (3:Fin 14) reversed
  have indexAt : reversed 3=List.replicate (store 4).length true:=by
    simp [reversed,scanned,activeLoopStore,prepared,e3]
  rw [indexAt,List.length_replicate] at cleaning
  have final : Function.update reversed 3 []=Function.update store 5
      (activeValues (store 0) (store 1) (store 2) 0 (store 4).length):=by
    funext r
    fin_cases r <;> simp [reversed,scanned,activeLoopStore,prepared,e3,e8,e13]
  rw [final] at cleaning
  have loopLimit : loopTime≤(store 4).length*(100*((store 0).length+(store 1).length+
      (store 2).length+(store 4).length+1)+2)+1:=by simpa [prepared,e3] using loopBound
  let S:=(store 0).length+(store 1).length+(store 2).length+(store 4).length+1
  have width : (store 4).length≤S:=by dsimp only [S];omega
  have loopLimit' : loopTime≤100*S^2+2*S+1:=by
    have bound : loopTime≤S*(100*S+2)+1:=loopLimit.trans
      (Nat.add_le_add_right (Nat.mul_le_mul_right _ width) 1)
    have expansion (x : Nat) : x*(100*x+2)+1=100*x^2+2*x+1:=by ring
    exact expansion S ▸ bound
  have linear : S≤S^2:=Nat.le_self_pow (by decide) _
  have positive : 1≤S^2:=Nat.one_le_pow _ _ (by dsimp only [S];omega)
  exact ⟨_,by change _≤1000*S^2;dsimp only [S] at loopLimit' linear positive ⊢;omega,
    copying.sequence (loopRun.sequence (reversing.sequence cleaning))⟩

end Counting.StackMachine.RealizabilityCheck
