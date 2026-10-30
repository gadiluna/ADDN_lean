import Counting.NetworkVistaCollectArrays

namespace Counting.StackMachine.NetworkVista
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- Preserve the previous-view array and the round matrix in registers
37 and 38. Only the measured binary bundle list is returned in register 27. -/
def collectPreserving : Routine 38 :=
  sequence (ofProgram (ListPrograms.copyProgram 37 37 21 0))
    (sequence (ofProgram (ListPrograms.copyProgram 37 38 22 0)) collectArrayBundles)

theorem collectPreserving_executes (store:Store 38) (accepted:Bool) (tail:List Bool)
    (status:store 1=accepted::tail) (empty:SenderEmpty store)
    (e21:store 21=[]) (e22:store 22=[]) (e24:store 24=[]) (e25:store 25=[]) (e26:store 26=[])
    (receiver:Nat) (pairs:List (Executable.Vista×Array Nat))
    (inside:∀pair∈pairs,receiver < pair.2.size)
    (viewInput:store 37=(Encoding.list Encoding.vista).encode (pairs.map Prod.fst))
    (rowInput:store 38=(Encoding.list (Encoding.array Encoding.natural)).encode (pairs.map Prod.snd))
    (position:(store 23).length=receiver) :
    ∃time ≤ Complexity.polynomial 26000 5
        ((store 37).length+(store 38).length+(store 23).length+pairs.length),
      Executes collectPreserving store time
        (Function.update store 27
          ((Encoding.list (Encoding.product Encoding.vista Encoding.natural)).encode (receivedPairs receiver pairs))) := by
  have zero:store 0=[]:=empty.1 0 (by decide) (by decide)
  have copyViews:=copy_executes 37 37 21 0 (by decide) (by decide) (by decide) store zero
  rw [e21,List.append_nil] at copyViews
  let copiedViews:=Function.update store 21 (store 37)
  have copyRows:=copy_executes 37 38 22 0 (by decide) (by decide) (by decide) copiedViews
    (by simp [copiedViews,zero])
  have source:copiedViews 38=store 38:=by simp [copiedViews]
  have target:copiedViews 22=[]:=by simp [copiedViews,e22]
  rw [source,target,List.append_nil] at copyRows
  let copied:=Function.update copiedViews 22 (store 38)
  have copiedEmpty:SenderEmpty copied:=by
    constructor
    · intro r small n1
      have n21:r≠21:=by intro same;subst r;norm_num at small
      have n22:r≠22:=by intro same;subst r;norm_num at small
      simpa [copied,copiedViews,n21,n22] using empty.1 r small n1
    · intro r low high
      have n21:r≠21:=by intro same;subst r;norm_num at low
      have n22:r≠22:=by intro same;subst r;norm_num at low
      simpa [copied,copiedViews,n21,n22] using empty.2 r low high
  obtain ⟨collectTime,collectBound,collectRun⟩:=collectArrayBundles_executes copied accepted tail
    (by simp [copied,copiedViews,status]) copiedEmpty
    (by simp [copied,copiedViews,e24]) (by simp [copied,copiedViews,e25])
    (by simp [copied,copiedViews,e26]) receiver pairs inside [] []
    (by simp [copied,copiedViews,viewInput]) (by simp [copied,rowInput])
    (by simp [copied,copiedViews,position])
  have final:collectBundlesStore copied receiver pairs [] []=
      Function.update store 27 ((Encoding.list (Encoding.product Encoding.vista Encoding.natural)).encode
        (receivedPairs receiver pairs)):=by
    funext r
    fin_cases r <;> simp [collectBundlesStore,copied,copiedViews,e21,e22,e26]
  rw [final] at collectRun
  have size21:(copied 21).length=(store 37).length:=by simp [copied,copiedViews]
  have size22:(copied 22).length=(store 38).length:=by simp [copied]
  have size23:(copied 23).length=(store 23).length:=by simp [copied,copiedViews]
  rw [size21,size22,size23] at collectBound
  let S:=(store 37).length+(store 38).length+(store 23).length+pairs.length+1
  have linear:S≤S^5:=Nat.le_self_pow (by decide) _
  have overhead:5*(store 37).length+5*(store 38).length+6≤6*S^5:=by
    calc
      _≤6*S:=by dsimp [S];omega
      _≤6*S^5:=Nat.mul_le_mul_left _ linear
  change collectTime≤25000*S^5 at collectBound
  refine ⟨5*(store 37).length+2+1+(5*(store 38).length+2+1+collectTime),?_,
    copyViews.sequence (copyRows.sequence collectRun)⟩
  change _≤26000*S^5
  omega

end Counting.StackMachine.NetworkVista
