import Counting.StackRealizabilityArcLoop

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- Produce one complete adjacency row. Unary positions are advanced by
physical pushes/copies, including the transposed incoming matrix address. -/
def arcRow : Routine 30:=sequence (ofProgram (ListPrograms.copyProgram 29 8 11 26))
  (sequence (ofProgram (ListPrograms.copyProgram 29 29 30 26))
    (sequence (forEach 30 arcItem) (sequence (clear 9) (sequence (clear 11) (pushBit 8 true)))))

def arcRowStore (store : Store 30) : Store 30:=
  Function.update (Function.update (Function.update store
    24 ((arcRowValues (arcTables store) (store 29).length (store 8).length 0
      (store 10).length (store 8).length (store 29).length).reverse++store 24))
    10 (List.replicate (store 29).length true++store 10))
    8 (true::store 8)

theorem arcRow_executes (store : Store 30)
    (flags : ∀r : Fin 32,12≤r.val → r.val<24 → store r=[])
    (e9 : store 9=[]) (e11 : store 11=[]) (e30 : store 30=[])
    (e26 : store 26=[]) (e27 : store 27=[]) (e28 : store 28=[]) :
    ∃ time ≤ 10000*(arcReadSize store+(store 29).length)^3,
      Executes arcRow store time (arcRowStore store):=by
  have copyIndex:=copy_executes 29 8 11 26 (by decide) (by decide) (by decide) store e26
  rw [e11,List.append_nil] at copyIndex
  let indexed:=Function.update store 11 (store 8)
  have copyWidth:=copy_executes 29 29 30 26 (by decide) (by decide) (by decide) indexed
    (by simp [indexed,e26])
  have atWidth : indexed 29=store 29:=by simp [indexed]
  have atCounter : indexed 30=[]:=by simp [indexed,e30]
  rw [atWidth,atCounter,List.append_nil] at copyWidth
  let prepared:=Function.update indexed 30 (store 29)
  have preparedFlags (r : Fin 32) (lo : 12≤r.val) (hi : r.val<24) : prepared r=[]:=by
    have n11 : r≠11:=by intro same;subst r;simp at lo
    have n30 : r≠30:=by intro same;subst r;simp at hi
    simp [prepared,indexed,n11,n30,flags r lo hi]
  obtain ⟨loopTime,loopBound,loopRun⟩:=arcLoop_executes prepared (store 29) (by simp [prepared]) preparedFlags
    (by simp [prepared,indexed,e26]) (by simp [prepared,indexed,e27]) (by simp [prepared,indexed,e28])
  let scanned:=arcLoopStore prepared (store 29)
  have clearY:=clear_executes (9:Fin 32) scanned
  have atY : scanned 9=List.replicate (store 29).length true:=by
    simp [scanned,arcLoopStore,prepared,indexed,e9]
  rw [atY,List.length_replicate] at clearY
  let clearedY:=Function.update scanned 9 []
  have clearYX:=clear_executes (11:Fin 32) clearedY
  have atYX : clearedY 11=(List.replicate (store 29).length (store 29)).flatten++store 8:=by
    simp [clearedY,scanned,arcLoopStore,prepared,indexed]
  rw [atYX,List.length_append,List.length_flatten,List.map_replicate,List.sum_replicate,smul_eq_mul] at clearYX
  let cleared:=Function.update clearedY 11 []
  have nextX:=pushBit_executes (8:Fin 32) true cleared
  have atX : cleared 8=store 8:=by simp [cleared,clearedY,scanned,arcLoopStore,prepared,indexed]
  rw [atX] at nextX
  have final : Function.update cleared 8 (true::store 8)=arcRowStore store:=by
    funext r
    fin_cases r <;> simp [cleared,clearedY,scanned,arcLoopStore,prepared,indexed,arcRowStore,
      e9,e11,e30]
  rw [final] at nextX
  have prepSize : arcReadSize prepared=arcReadSize store+(store 8).length:=by
    simp [arcReadSize,prepared,indexed,e11]
    omega
  have prepWidth : prepared 29=store 29:=by simp [prepared,indexed]
  rw [prepSize,prepWidth] at loopBound
  let S:=arcReadSize store+(store 29).length
  have positive : 1≤S:=by dsimp only [S,arcReadSize];omega
  have width : (store 29).length≤S:=by dsimp only [S];omega
  have xBound : (store 8).length≤S:=by dsimp only [S,arcReadSize];omega
  have baseBound : arcReadSize store+(store 8).length+(store 29).length+
      (store 29).length*((store 29).length+2)≤5*S^2:=by
    have product:=Nat.mul_le_mul width (show (store 29).length+2≤3*S by omega)
    have linear : S≤S^2:=Nat.le_self_pow (by decide) _
    have reassoc : arcReadSize store+(store 8).length+(store 29).length=S+(store 8).length:=by
      dsimp only [S];omega
    rw [reassoc]
    nlinarith only [product,linear,xBound]
  have loopLimit : loopTime≤5500*S^3+2*S+1:=by
    have bound : loopTime≤S*(1100*(5*S^2)+2)+1:=loopBound.trans
      (Nat.add_le_add_right (Nat.mul_le_mul width (Nat.add_le_add_right
        (Nat.mul_le_mul_left _ baseBound) 2)) 1)
    have expansion (x : Nat) : x*(1100*(5*x^2)+2)+1=5500*x^3+2*x+1:=by ring
    exact expansion S ▸ bound
  have square : (store 29).length*(store 29).length≤S^3:=by
    calc
      _≤S*S:=Nat.mul_le_mul width width
      _=S^2:=(pow_two S).symm
      _≤S^3:=Nat.pow_le_pow_right positive (by decide)
  have linear : S≤S^3:=Nat.le_self_pow (by decide) _
  have one : 1≤S^3:=Nat.one_le_pow _ _ positive
  have execution:=copyIndex.sequence (copyWidth.sequence (loopRun.sequence (clearY.sequence (clearYX.sequence nextX))))
  exact ⟨_,by change _≤10000*S^3;dsimp only [S] at loopLimit square linear one ⊢;omega,execution⟩

end Counting.StackMachine.RealizabilityCheck
