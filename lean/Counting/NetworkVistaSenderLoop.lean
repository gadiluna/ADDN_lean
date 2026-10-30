import Counting.NetworkVistaSenderItem
import Counting.NetworkVistaSenderStore
import Counting.NetworkVistaBundleValues

namespace Counting.StackMachine.NetworkVista
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

def senderLoopStore (store:Store 38) (receiver:Nat) (pairs:List (Executable.Vista×Array Nat))
    (viewSuffix rowSuffix:List Bool) : Store 38 :=
  Function.update (Function.update (Function.update (Function.update (Function.update store
    21 viewSuffix) 22 rowSuffix) 26 [])
    24 ((Encoding.sequence (Encoding.product Encoding.vista Encoding.natural) (receivedPairs receiver pairs)).reverse++store 24))
    25 (List.replicate (receivedPairs receiver pairs).length true++store 25)

theorem senderLoop_executes (store:Store 38) (accepted:Bool) (tail:List Bool)
    (status:store 1=accepted::tail) (empty:SenderEmpty store)
    (receiver:Nat) (pairs:List (Executable.Vista×Array Nat))
    (inside:∀pair∈pairs,receiver < pair.2.size)
    (viewSuffix rowSuffix:List Bool)
    (viewInput:store 21=Encoding.sequence Encoding.vista (pairs.map Prod.fst)++viewSuffix)
    (rowInput:store 22=Encoding.sequence (Encoding.array Encoding.natural) (pairs.map Prod.snd)++rowSuffix)
    (position:(store 23).length=receiver)
    (counter:store 26=List.replicate pairs.length true) :
    ∃time ≤ pairs.length*(3*Complexity.polynomial DagParser.vista.coefficient DagParser.vista.exponent (store 21).length+
        3*Complexity.polynomial NetworkRecognition.row.coefficient NetworkRecognition.row.exponent (store 22).length+
        100*((store 21).length+(store 22).length+(store 23).length+1)+2)+1,
      Executes (forEach 26 senderItem) store time (senderLoopStore store receiver pairs viewSuffix rowSuffix) := by
  induction pairs generalizing store with
  | nil=>
    have countEmpty:store 26=[]:=by simpa using counter
    have viewEmpty:store 21=viewSuffix:=by simpa [Encoding.sequence] using viewInput
    have rowEmpty:store 22=rowSuffix:=by simpa [Encoding.sequence] using rowInput
    obtain ⟨ran,halted⟩:=repeat_empty (26:Fin 40) senderItem store countEmpty
    have final:senderLoopStore store receiver [] viewSuffix rowSuffix=store:=by
      funext r
      fin_cases r <;> simp [senderLoopStore,receivedPairs,Encoding.sequence,viewEmpty,rowEmpty,countEmpty]
    exact ⟨1,by simp,⟨1,store⟩,ran,halted,final.symm⟩
  | cons pair pairs ih=>
    obtain ⟨vista,row⟩:=pair
    let restViews:=Encoding.sequence Encoding.vista (pairs.map Prod.fst)++viewSuffix
    let restRows:=Encoding.sequence (Encoding.array Encoding.natural) (pairs.map Prod.snd)++rowSuffix
    let consumed:=Function.update store 26 (List.replicate pairs.length true)
    have consumedEmpty:SenderEmpty consumed:=by
      constructor
      · intro r small n1
        have n26:r≠26:=by intro same;subst r;norm_num at small
        simpa [consumed,n26] using empty.1 r small n1
      · intro r low high
        have n26:r≠26:=by intro same;subst r;norm_num at low
        simpa [consumed,n26] using empty.2 r low high
    have inRange:receiver < row.size:=inside (vista,row) (by simp)
    let index:Fin row.size:=⟨receiver,inRange⟩
    obtain ⟨bodyTime,bodyBound,body,bodyRun,bodyHalted,bodyStore⟩:=senderItem_executes consumed accepted tail
      (by simp [consumed,status]) consumedEmpty vista row index restViews restRows
      (by simpa [consumed,restViews,Encoding.sequence,List.append_assoc] using viewInput)
      (by simpa [consumed,restRows,Encoding.sequence,List.append_assoc] using rowInput)
      (by simpa [consumed] using position)
    let middle:=senderItemStore consumed vista row[receiver] restViews restRows
    have middleStatus:middle 1=accepted::tail:=by simp [middle,senderItemStore,ite_apply,consumed,status]
    have middleEmpty:SenderEmpty middle:=senderItemStore_empty _ _ _ _ _ consumedEmpty
    have middlePosition:(middle 23).length=receiver:=by simpa [middle,senderItemStore,ite_apply,consumed] using position
    have middleCounter:middle 26=List.replicate pairs.length true:=by simp [middle,senderItemStore,ite_apply,consumed]
    obtain ⟨tailTime,tailBound,finish,tailRun,tailHalted,tailStore⟩:=ih middle middleStatus middleEmpty
      (by intro pair present;exact inside pair (by simp [present]))
      (by simp [middle,senderItemStore,ite_apply,restViews]) (by simp [middle,senderItemStore,ite_apply,restRows]) middlePosition middleCounter
    have firstRun:=repeat_iteration (26:Fin 40) senderItem store true (List.replicate pairs.length true)
      (by simpa only [List.length_cons,List.replicate_succ] using counter) bodyTime body bodyRun bodyHalted
    have selected:(row[receiver]?).getD 0=row[receiver]:=by
      simp only [Array.getElem?_eq_getElem inRange,Option.getD_some]
    have final:senderLoopStore middle receiver pairs viewSuffix rowSuffix=
        senderLoopStore store receiver ((vista,row)::pairs) viewSuffix rowSuffix:=by
      funext r
      by_cases zero:row[receiver]=0
      all_goals by_cases n21:r=21 <;> by_cases n22:r=22 <;> by_cases n24:r=24 <;>
        by_cases n25:r=25 <;> by_cases n26:r=26 <;>
        simp [senderLoopStore,receivedPairs,middle,senderItemStore,consumed,selected,zero,
          n21,n22,n24,n25,n26,Encoding.sequence,List.reverse_append,List.append_assoc,List.replicate_succ,bundleReplicatePush]
    have viewShorter:(middle 21).length≤(store 21).length:=by
      simp only [middle,senderItemStore_viewSuffix]
      rw [viewInput]
      simp only [List.map_cons,Encoding.sequence,List.length_append,restViews]
      omega
    have rowShorter:(middle 22).length≤(store 22).length:=by
      simp only [middle,senderItemStore_rowSuffix]
      rw [rowInput]
      simp only [List.map_cons,Encoding.sequence,List.length_append,restRows]
      omega
    have sameIndex:middle 23=store 23:=by simp [middle,senderItemStore,ite_apply,consumed]
    rw [sameIndex] at tailBound
    have tailLimit:tailTime≤pairs.length*(3*Complexity.polynomial DagParser.vista.coefficient DagParser.vista.exponent (store 21).length+
        3*Complexity.polynomial NetworkRecognition.row.coefficient NetworkRecognition.row.exponent (store 22).length+
        100*((store 21).length+(store 22).length+(store 23).length+1)+2)+1:=by
      apply tailBound.trans
      unfold Complexity.polynomial
      gcongr
    simp only [consumed,Function.update_of_ne (by decide : (21:Fin 40)≠26),
      Function.update_of_ne (by decide : (22:Fin 40)≠26),
      Function.update_of_ne (by decide : (23:Fin 40)≠26)] at bodyBound
    refine ⟨bodyTime+2+tailTime,?_,finish,?_,tailHalted,tailStore.trans final⟩
    · simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
    · rw [Machine.run_add,firstRun,Option.bind_some,bodyStore]
      exact tailRun

end Counting.StackMachine.NetworkVista
