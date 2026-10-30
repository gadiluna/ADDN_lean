import Counting.NetworkVistaSenderBounds
import Counting.NetworkVistaBundleFinish
import Counting.NetworkVistaBundleBounds

namespace Counting.StackMachine.NetworkVista
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

def collectBundles : Routine 38 := sequence (forEach 26 senderItem) finishBundles

def collectBundlesStore (store:Store 38) (receiver:Nat) (pairs:List (Executable.Vista×Array Nat))
    (viewSuffix rowSuffix:List Bool) : Store 38 :=
  Function.update (Function.update (Function.update (Function.update store 21 viewSuffix) 22 rowSuffix) 26 [])
    27 ((Encoding.list (Encoding.product Encoding.vista Encoding.natural)).encode (receivedPairs receiver pairs))

/-- Complete physical collection of the compact received-message list.
The cost includes both typed streams, every binary arc lookup, zero-edge
filtering, measured list length, and final serialization. -/
theorem collectBundles_executes (store:Store 38) (accepted:Bool) (tail:List Bool)
    (status:store 1=accepted::tail) (empty:SenderEmpty store)
    (e24:store 24=[]) (e25:store 25=[])
    (receiver:Nat) (pairs:List (Executable.Vista×Array Nat))
    (inside:∀pair∈pairs,receiver < pair.2.size)
    (viewSuffix rowSuffix:List Bool)
    (viewInput:store 21=Encoding.sequence Encoding.vista (pairs.map Prod.fst)++viewSuffix)
    (rowInput:store 22=Encoding.sequence (Encoding.array Encoding.natural) (pairs.map Prod.snd)++rowSuffix)
    (position:(store 23).length=receiver)
    (counter:store 26=List.replicate pairs.length true) :
    ∃time ≤ Complexity.polynomial 20000 5
        ((store 21).length+(store 22).length+(store 23).length+pairs.length),
      Executes collectBundles store time (collectBundlesStore store receiver pairs viewSuffix rowSuffix) := by
  obtain ⟨loopTime,loopBound,loopRun⟩:=senderLoop_executes_polynomial store accepted tail status empty
    receiver pairs inside viewSuffix rowSuffix viewInput rowInput position counter
  let scanned:=senderLoopStore store receiver pairs viewSuffix rowSuffix
  let messages:=receivedPairs receiver pairs
  have stream:scanned 24=(Encoding.sequence (Encoding.product Encoding.vista Encoding.natural) messages).reverse:=by
    simp [scanned,senderLoopStore,messages,e24]
  have count:scanned 25=List.replicate messages.length true:=by simp [scanned,senderLoopStore,messages,e25]
  have clean (r:Fin 40) (member:r∈({27,28,29,30}:Finset (Fin 40))):scanned r=[]:=by
    fin_cases r
    all_goals simp only [Finset.mem_insert,Finset.mem_singleton] at member
    all_goals first | contradiction | simp [scanned,senderLoopStore,empty.2]
  obtain ⟨finishTime,finishBound,finishRun⟩:=finishBundles_executes scanned messages stream count clean
  have final:Function.update (Function.update (Function.update scanned 24 []) 25 [])
      27 ((Encoding.list (Encoding.product Encoding.vista Encoding.natural)).encode messages)=
        collectBundlesStore store receiver pairs viewSuffix rowSuffix:=by
    funext r
    fin_cases r <;> simp [scanned,senderLoopStore,collectBundlesStore,messages,e24,e25]
  rw [final] at finishRun
  let S:=(store 21).length+(store 22).length+(store 23).length+pairs.length+1
  have positive:1≤S:=by dsimp [S];omega
  have codeBound:(Encoding.sequence (Encoding.product Encoding.vista Encoding.natural) messages).length≤
      (store 21).length+(store 22).length:=by
    apply (receivedPairs_code_length_le receiver pairs).trans
    rw [viewInput,rowInput,List.length_append,List.length_append]
    omega
  have countBound:messages.length≤pairs.length:=receivedPairs_length_le receiver pairs
  rw [stream,count,List.length_reverse,List.length_replicate] at finishBound
  have finishLimit:finishTime≤30*S^2:=by
    apply finishBound.trans
    gcongr
    dsimp [S]
    omega
  have square:S^2≤S^5:=Nat.pow_le_pow_right positive (by decide)
  have one:1≤S^5:=Nat.one_le_pow _ _ positive
  change loopTime≤18000*S^5 at loopBound
  refine ⟨loopTime+1+finishTime,?_,loopRun.sequence finishRun⟩
  change loopTime+1+finishTime≤20000*S^5
  omega

end Counting.StackMachine.NetworkVista
