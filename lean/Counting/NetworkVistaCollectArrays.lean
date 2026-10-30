import Counting.NetworkVistaCollectHeader

namespace Counting.StackMachine.NetworkVista
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def collectArrayBundles : Routine 38 := sequence collectViewHeader
  (sequence collectRowHeader collectBundles)

/-- Two actual serialized arrays are traversed together; their length
headers are read by the machine before the sender loop starts. -/
theorem collectArrayBundles_executes (store:Store 38) (accepted:Bool) (tail:List Bool)
    (status:store 1=accepted::tail) (empty:SenderEmpty store)
    (e24:store 24=[]) (e25:store 25=[]) (e26:store 26=[])
    (receiver:Nat) (pairs:List (Executable.Vista×Array Nat))
    (inside:∀pair∈pairs,receiver < pair.2.size)
    (viewSuffix rowSuffix:List Bool)
    (viewInput:store 21=(Encoding.list Encoding.vista).encode (pairs.map Prod.fst)++viewSuffix)
    (rowInput:store 22=(Encoding.list (Encoding.array Encoding.natural)).encode (pairs.map Prod.snd)++rowSuffix)
    (position:(store 23).length=receiver) :
    ∃time ≤ Complexity.polynomial 25000 5
        ((store 21).length+(store 22).length+(store 23).length+pairs.length),
      Executes collectArrayBundles store time (collectBundlesStore store receiver pairs viewSuffix rowSuffix) := by
  obtain ⟨viewTime,viewBound,viewRun⟩:=collectViewHeader_executes store accepted tail status empty e26
    (pairs.map Prod.fst) viewSuffix viewInput
  let viewed:=Function.update (Function.update store 21
    (Encoding.sequence Encoding.vista (pairs.map Prod.fst)++viewSuffix)) 26 (List.replicate pairs.length true)
  have viewedRun:Executes collectViewHeader store viewTime viewed:=by
    simpa only [List.length_map] using viewRun
  have viewedStatus:viewed 1=accepted::tail:=by simp [viewed,status]
  have viewedEmpty:SenderEmpty viewed:=by
    constructor
    · intro r small n1
      have n21:r≠21:=by intro same;subst r;norm_num at small
      have n26:r≠26:=by intro same;subst r;norm_num at small
      simpa [viewed,n21,n26] using empty.1 r small n1
    · intro r low high
      have n21:r≠21:=by intro same;subst r;norm_num at low
      have n26:r≠26:=by intro same;subst r;norm_num at low
      simpa [viewed,n21,n26] using empty.2 r low high
  have viewedRows:viewed 22=(Encoding.list (Encoding.array Encoding.natural)).encode
      (pairs.map Prod.snd)++rowSuffix:=by simp [viewed,rowInput]
  obtain ⟨rowTime,rowBound,rowRun⟩:=collectRowHeader_executes viewed accepted tail viewedStatus viewedEmpty
    (pairs.map Prod.snd) rowSuffix viewedRows
  let prepared:=Function.update viewed 22
    (Encoding.sequence (Encoding.array Encoding.natural) (pairs.map Prod.snd)++rowSuffix)
  have preparedEmpty:SenderEmpty prepared:=by
    constructor
    · intro r small n1
      have n22:r≠22:=by intro same;subst r;norm_num at small
      simpa [prepared,n22] using viewedEmpty.1 r small n1
    · intro r low high
      have n22:r≠22:=by intro same;subst r;norm_num at low
      simpa [prepared,n22] using viewedEmpty.2 r low high
  obtain ⟨collectTime,collectBound,collectRun⟩:=collectBundles_executes prepared accepted tail
    (by simp [prepared,viewed,status]) preparedEmpty
    (by simp [prepared,viewed,e24]) (by simp [prepared,viewed,e25]) receiver pairs inside viewSuffix rowSuffix
    (by simp [prepared,viewed]) (by simp [prepared]) (by simp [prepared,viewed,position])
    (by simp [prepared,viewed])
  have final:collectBundlesStore prepared receiver pairs viewSuffix rowSuffix=
      collectBundlesStore store receiver pairs viewSuffix rowSuffix:=by
    funext r
    fin_cases r <;> simp [collectBundlesStore,prepared,viewed]
  rw [final] at collectRun
  have viewSize:(prepared 21).length≤(store 21).length:=by
    simp only [prepared,viewed,Function.update_of_ne (by decide : (21:Fin 40)≠22),
      Function.update_of_ne (by decide : (21:Fin 40)≠26),Function.update_self]
    rw [viewInput]
    change _≤((Encoding.frame (pairs.map Prod.fst).length.bits++
      Encoding.sequence Encoding.vista (pairs.map Prod.fst))++viewSuffix).length
    simp only [List.length_append];omega
  have rowSize:(prepared 22).length≤(store 22).length:=by
    simp only [prepared,Function.update_self]
    rw [rowInput]
    change _≤((Encoding.frame (pairs.map Prod.snd).length.bits++
      Encoding.sequence (Encoding.array Encoding.natural) (pairs.map Prod.snd))++rowSuffix).length
    simp only [List.length_append];omega
  have positionSize:(prepared 23).length=(store 23).length:=by simp [prepared,viewed]
  have rowSource:(viewed 22).length=(store 22).length:=by simp [viewed]
  rw [rowSource] at rowBound
  let S:=(store 21).length+(store 22).length+(store 23).length+pairs.length+1
  have positive:1≤S:=by dsimp [S];omega
  have cubic:S^3≤S^5:=Nat.pow_le_pow_right positive (by decide)
  have viewLimit:viewTime≤1820*S^5:=by
    apply viewBound.trans
    apply Nat.mul_le_mul_left
    apply le_trans _ cubic
    dsimp [S];gcongr;omega
  have rowLimit:rowTime≤1830*S^5:=by
    apply rowBound.trans
    apply Nat.mul_le_mul_left
    apply le_trans _ cubic
    dsimp [S];gcongr;omega
  have collectLimit:collectTime≤20000*S^5:=by
    apply collectBound.trans
    simp only [Complexity.polynomial,positionSize]
    dsimp [S]
    gcongr
  have one:1≤S^5:=Nat.one_le_pow _ _ positive
  refine ⟨viewTime+1+(rowTime+1+collectTime),?_,viewedRun.sequence (rowRun.sequence collectRun)⟩
  change viewTime+1+(rowTime+1+collectTime)≤25000*S^5
  omega

end Counting.StackMachine.NetworkVista
