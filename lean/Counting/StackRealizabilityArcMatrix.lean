import Counting.StackRealizabilityArcRows

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

/-- Eight input tables and explicit unary width are preserved. The result is
a row-major matrix in register 30; all indexing work is initialized and cleared. -/
def arcMatrix : Routine 30:=sequence (ofProgram (ListPrograms.copyProgram 29 29 31 26))
  (sequence (forEach 31 arcRow)
    (sequence (ofProgram (ListPrograms.reverseProgram 30 24 30))
      (sequence (clear 8) (clear 10))))

def ArcWorkspaceEmpty (store : Store 30) : Prop:=
  ∀r : Fin 32,8≤r.val → r≠25 → r≠29 → store r=[]

theorem arcMatrix_executes (store : Store 30) (empty : ArcWorkspaceEmpty store) :
    ∃ time ≤ 1000000*(arcReadSize store+(store 29).length)^7,
      Executes arcMatrix store time (Function.update store 30
        (arcTableValues (arcTables store) (store 29).length 0 0 (store 29).length)):=by
  unfold ArcWorkspaceEmpty at empty
  have e8 : store 8=[]:=empty 8 (by decide) (by decide) (by decide)
  have e10 : store 10=[]:=empty 10 (by decide) (by decide) (by decide)
  have e24 : store 24=[]:=empty 24 (by decide) (by decide) (by decide)
  have e31 : store 31=[]:=empty 31 (by decide) (by decide) (by decide)
  have copyWidth:=copy_executes 29 29 31 26 (by decide) (by decide) (by decide) store
    (empty 26 (by decide) (by decide) (by decide))
  rw [e31,List.append_nil] at copyWidth
  let prepared:=Function.update store 31 (store 29)
  have work (r : Fin 32) (lo : 12≤r.val) (hi : r.val<24) : prepared r=[]:=by
    have n25 : r≠25:=by intro same;subst r;simp at hi
    have n29 : r≠29:=by intro same;subst r;simp at hi
    have n31 : r≠31:=by intro same;subst r;simp at hi
    simp [prepared,n31,empty r (by omega) n25 n29]
  obtain ⟨loopTime,loopBound,loopRun⟩:=arcRows_executes prepared (store 29) (by simp [prepared]) work
    (by simp [prepared,empty]) (by simp [prepared,empty]) (by simp [prepared,empty])
    (by simp [prepared,empty]) (by simp [prepared,empty]) (by simp [prepared,empty])
  let scanned:=arcRowsStore prepared (store 29)
  have reverseOutput:=reverse_executes 30 24 30 (by decide) scanned
  have matrixAt : scanned 24=(arcTableValues (arcTables store) (store 29).length 0 0 (store 29).length).reverse:=by
    simp [scanned,arcRowsStore,prepared,e8,e10,e24]
  have outputEmpty : scanned 30=[]:=by simp [scanned,arcRowsStore,prepared,empty]
  rw [matrixAt,outputEmpty,List.append_nil,List.reverse_reverse,List.length_reverse,arcTableValues_length] at reverseOutput
  let reversed:=Function.update (Function.update scanned 24 []) 30
    (arcTableValues (arcTables store) (store 29).length 0 0 (store 29).length)
  have clearX:=clear_executes (8:Fin 32) reversed
  have xAt : reversed 8=List.replicate (store 29).length true:=by simp [reversed,scanned,arcRowsStore,prepared,e8]
  rw [xAt,List.length_replicate] at clearX
  let clearedX:=Function.update reversed 8 []
  have clearXY:=clear_executes (10:Fin 32) clearedX
  have xyAt : clearedX 10=(List.replicate (store 29).length (List.replicate (store 29).length true)).flatten:=by
    simp [clearedX,reversed,scanned,arcRowsStore,prepared,e10]
  rw [xyAt,List.length_flatten,List.map_replicate,List.length_replicate,List.sum_replicate,smul_eq_mul] at clearXY
  have final : Function.update clearedX 10 []=Function.update store 30
      (arcTableValues (arcTables store) (store 29).length 0 0 (store 29).length):=by
    funext r
    fin_cases r <;> simp [clearedX,reversed,scanned,arcRowsStore,prepared,empty]
  rw [final] at clearXY
  have preSize : arcReadSize prepared=arcReadSize store:=by simp [arcReadSize,prepared]
  have preWidth : prepared 29=store 29:=by simp [prepared]
  rw [preSize,preWidth] at loopBound
  let S:=arcReadSize store+(store 29).length
  have positive : 1≤S:=by dsimp only [S,arcReadSize];omega
  have width : (store 29).length≤S:=by dsimp only [S];omega
  have base : S+(store 29).length*((store 29).length+1)≤3*S^2:=by
    have product:=Nat.mul_le_mul width (show (store 29).length+1≤2*S by omega)
    have linear : S≤S^2:=Nat.le_self_pow (by decide) _
    nlinarith only [product,linear]
  have loopLimit : loopTime≤270000*S^7+2*S+1:=by
    have bound : loopTime≤S*(10000*(3*S^2)^3+2)+1:=loopBound.trans
      (Nat.add_le_add_right (Nat.mul_le_mul width (Nat.add_le_add_right
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left base 3)) 2)) 1)
    have expansion (x : Nat) : x*(10000*(3*x^2)^3+2)+1=270000*x^7+2*x+1:=by ring
    exact expansion S ▸ bound
  have square : (store 29).length*(store 29).length≤S^7:=by
    calc
      _≤S*S:=Nat.mul_le_mul width width
      _=S^2:=(pow_two S).symm
      _≤S^7:=Nat.pow_le_pow_right positive (by decide)
  have linear : S≤S^7:=Nat.le_self_pow (by decide) _
  have one : 1≤S^7:=Nat.one_le_pow _ _ positive
  have execution:=copyWidth.sequence (loopRun.sequence (reverseOutput.sequence (clearX.sequence clearXY)))
  exact ⟨_,by change _≤1000000*S^7;dsimp only [S] at loopLimit square linear one ⊢;omega,execution⟩

end Counting.StackMachine.RealizabilityCheck
