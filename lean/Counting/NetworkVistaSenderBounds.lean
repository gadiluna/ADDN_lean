import Counting.NetworkVistaSenderLoop

namespace Counting.StackMachine.NetworkVista
open Routine EncodingPrograms

theorem rowParser_coefficient : NetworkRecognition.row.coefficient=1860 := rfl
theorem rowParser_exponent : NetworkRecognition.row.exponent=3 := rfl

theorem senderLoop_executes_polynomial (store:Store 38) (accepted:Bool) (tail:List Bool)
    (status:store 1=accepted::tail) (empty:SenderEmpty store)
    (receiver:Nat) (pairs:List (Executable.Vista×Array Nat))
    (inside:∀pair∈pairs,receiver < pair.2.size)
    (viewSuffix rowSuffix:List Bool)
    (viewInput:store 21=Encoding.sequence Encoding.vista (pairs.map Prod.fst)++viewSuffix)
    (rowInput:store 22=Encoding.sequence (Encoding.array Encoding.natural) (pairs.map Prod.snd)++rowSuffix)
    (position:(store 23).length=receiver)
    (counter:store 26=List.replicate pairs.length true) :
    ∃time ≤ Complexity.polynomial 18000 5
        ((store 21).length+(store 22).length+(store 23).length+pairs.length),
      Executes (forEach 26 senderItem) store time (senderLoopStore store receiver pairs viewSuffix rowSuffix) := by
  obtain ⟨time,bound,run⟩:=senderLoop_executes store accepted tail status empty receiver pairs inside
    viewSuffix rowSuffix viewInput rowInput position counter
  simp only [DagParser.vista_coefficient,DagParser.vista_exponent,rowParser_coefficient,rowParser_exponent,
    Complexity.polynomial] at bound
  let S:=(store 21).length+(store 22).length+(store 23).length+pairs.length+1
  have positive:1≤S:=by dsimp [S];omega
  have v:((store 21).length+1)^4≤S^4:=by dsimp [S];gcongr;omega
  have r:((store 22).length+1)^3≤S^4:=by
    calc
      _≤S^3:=by dsimp [S];gcongr;omega
      _≤S^4:=Nat.pow_le_pow_right positive (by decide)
  have linear:(store 21).length+(store 22).length+(store 23).length+1≤S^4:=by
    apply le_trans _ (Nat.le_self_pow (by decide : 4 ≠ 0) S)
    dsimp [S];omega
  have one:1≤S^4:=Nat.one_le_pow _ _ positive
  have body:3*(3890*((store 21).length+1)^4)+3*(1860*((store 22).length+1)^3)+
      100*((store 21).length+(store 22).length+(store 23).length+1)+2≤17352*S^4:=by omega
  have number:pairs.length≤S:=by dsimp [S];omega
  have total:time≤S*(17352*S^4)+1:=by
    apply bound.trans
    gcongr
  have expression:S*(17352*S^4)=17352*S^5:=by ring
  rw [expression] at total
  have last:1≤S^5:=Nat.one_le_pow _ _ positive
  refine ⟨time,?_,run⟩
  change time≤18000*S^5
  omega

end Counting.StackMachine.NetworkVista
