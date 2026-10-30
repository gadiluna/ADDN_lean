import Counting.NetworkVistaSenderLayout

namespace Counting.StackMachine.NetworkVista
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

theorem senderItem_executes (store:Store 38) (accepted:Bool) (tail:List Bool)
    (status:store 1=accepted::tail) (empty:SenderEmpty store)
    (vista:Executable.Vista) (row:Array Nat) (index:Fin row.size)
    (viewSuffix rowSuffix:List Bool)
    (viewInput:store 21=Encoding.vista.encode vista++viewSuffix)
    (rowInput:store 22=(Encoding.array Encoding.natural).encode row++rowSuffix)
    (position:(store 23).length=index.val) :
    ∃time ≤ 3*Complexity.polynomial DagParser.vista.coefficient DagParser.vista.exponent (store 21).length+
        3*Complexity.polynomial NetworkRecognition.row.coefficient NetworkRecognition.row.exponent (store 22).length+
        100*((store 21).length+(store 22).length+(store 23).length+1),
      Executes senderItem store time (senderItemStore store vista row[index.val] viewSuffix rowSuffix) := by
  let viewLocal:=store ∘ senderViewRoles
  obtain ⟨viewTime,viewBound,viewRun⟩:=Forward.parseForward_canonical DagParser.vista viewLocal accepted tail
    status (senderView_work store empty)
    (empty.1 2 (by decide) (by decide)) (empty.2 27 (by decide) (by decide)) vista viewSuffix viewInput
  let viewed:=Function.update (Function.update store 21 viewSuffix) 27 (Encoding.vista.encode vista)
  have viewing:Executes (relocate (Forward.parseForward DagParser.vista) senderViewRoles) store viewTime viewed:=by
    apply relocate_executes_frame (Forward.parseForward DagParser.vista) senderViewRoles store viewed viewLocal
      (Function.update (Function.update viewLocal 17 viewSuffix) 19 (Encoding.vista.encode vista)) viewTime rfl
    · intro r
      fin_cases r <;> simp [viewed,viewLocal,senderViewRoles]
    · intro r outside
      have n21:r≠21:=by simpa [senderViewRoles] using (outside 17).symm
      have n27:r≠27:=by simpa [senderViewRoles] using (outside 19).symm
      simp [viewed,n21,n27]
    · exact viewRun
  let rowLocal:=viewed ∘ senderRowRoles
  have rowWork (r:Fin 20) (member:r∈(Forward.wideParser NetworkRecognition.row).work):rowLocal r=[]:=by
    have old:=senderRow_work store empty r member
    obtain ⟨small,_⟩:=Forward.work_small NetworkRecognition.row r member
    fin_cases r
    all_goals first | omega | simpa [rowLocal,viewed,senderRowRoles] using old
  obtain ⟨rowTime,rowBound,rowRun⟩:=Forward.parseForward_canonical NetworkRecognition.row rowLocal accepted tail
    (by simp [rowLocal,viewed,senderRowRoles,status]) rowWork
    (by simpa [rowLocal,viewed,senderRowRoles] using empty.1 2 (by decide) (by decide))
    (by simpa [rowLocal,viewed,senderRowRoles] using empty.2 28 (by decide) (by decide)) row rowSuffix
    (by simpa [rowLocal,viewed,senderRowRoles] using rowInput)
  let decoded:=Function.update (Function.update viewed 22 rowSuffix) 28 ((Encoding.array Encoding.natural).encode row)
  have rowReading:Executes (relocate (Forward.parseForward NetworkRecognition.row) senderRowRoles) viewed rowTime decoded:=by
    apply relocate_executes_frame (Forward.parseForward NetworkRecognition.row) senderRowRoles viewed decoded rowLocal
      (Function.update (Function.update rowLocal 17 rowSuffix) 19 ((Encoding.array Encoding.natural).encode row)) rowTime rfl
    · intro r
      fin_cases r <;> simp [decoded,rowLocal,senderRowRoles]
    · intro r outside
      have n22:r≠22:=by simpa [senderRowRoles] using (outside 17).symm
      have n28:r≠28:=by simpa [senderRowRoles] using (outside 19).symm
      simp [decoded,n22,n28]
    · exact rowRun
  let bundleLocal:=decoded ∘ senderBundleRoles
  have bundleEmpty (r:Fin 16) (member:r∈({5,6,7,8,9,10,11,12}:Finset (Fin 16))):bundleLocal r=[]:=by
    fin_cases r
    all_goals simp only [Finset.mem_insert,Finset.mem_singleton] at member
    all_goals first | contradiction | simp [bundleLocal,decoded,viewed,senderBundleRoles,empty.2]
  obtain ⟨bundleTime,bundleBound,bundleRun⟩:=appendReceivedBundle_executes bundleLocal vista row index
    (by simp [bundleLocal,decoded,viewed,senderBundleRoles])
    (by simp [bundleLocal,decoded,senderBundleRoles])
    (by simpa [bundleLocal,decoded,viewed,senderBundleRoles] using position) bundleEmpty
  let sent:=if row[index.val]=0 then decoded else
    Function.update (Function.update decoded 24
      (((Encoding.product Encoding.vista Encoding.natural).encode (vista,row[index.val])).reverse++store 24))
      25 (true::store 25)
  have sending:Executes (relocate appendReceivedBundle senderBundleRoles) decoded bundleTime sent:=by
    apply relocate_executes_frame appendReceivedBundle senderBundleRoles decoded sent bundleLocal
      (receivedBundleStore bundleLocal vista row[index.val]) bundleTime rfl
    · intro r
      fin_cases r <;> simp [sent,receivedBundleStore,ite_apply,bundleLocal,senderBundleRoles,decoded,viewed]
    · intro r outside
      have n24:r≠24:=by simpa [senderBundleRoles] using (outside 3).symm
      have n25:r≠25:=by simpa [senderBundleRoles] using (outside 4).symm
      simp [sent,ite_apply,n24,n25]
    · exact bundleRun
  have viewClear:=clear_executes (27:Fin 40) sent
  have viewAt:sent 27=Encoding.vista.encode vista:=by simp [sent,ite_apply,decoded,viewed]
  rw [viewAt] at viewClear
  have rowClear:=clear_executes (28:Fin 40) (Function.update sent 27 [])
  have rowAt:Function.update sent 27 [] 28=(Encoding.array Encoding.natural).encode row:=by simp [sent,ite_apply,decoded,viewed]
  rw [rowAt] at rowClear
  have final:Function.update (Function.update sent 27 []) 28 []=senderItemStore store vista row[index.val] viewSuffix rowSuffix:=by
    funext r
    by_cases zero:row[index.val]=0
    all_goals by_cases n21:r=21 <;> by_cases n22:r=22 <;> by_cases n24:r=24 <;>
      by_cases n25:r=25 <;> by_cases n27:r=27 <;> by_cases n28:r=28 <;>
      simp [senderItemStore,sent,decoded,viewed,zero,n21,n22,n24,n25,n27,n28,
        empty.2 27 (by decide) (by decide),empty.2 28 (by decide) (by decide)]
  rw [final] at rowClear
  have viewLength:(Encoding.vista.encode vista).length≤(store 21).length:=by rw [viewInput,List.length_append];omega
  have rowLength:((Encoding.array Encoding.natural).encode row).length≤(store 22).length:=by rw [rowInput,List.length_append];omega
  change viewTime≤3*Complexity.polynomial DagParser.vista.coefficient DagParser.vista.exponent (store 21).length+2 at viewBound
  have rowSource:rowLocal 17=store 22:=by simp [rowLocal,viewed,senderRowRoles]
  rw [rowSource] at rowBound
  have v:bundleLocal 0=Encoding.vista.encode vista:=by simp [bundleLocal,decoded,viewed,senderBundleRoles]
  have r:bundleLocal 1=(Encoding.array Encoding.natural).encode row:=by simp [bundleLocal,decoded,senderBundleRoles]
  have i:bundleLocal 2=store 23:=by simp [bundleLocal,decoded,viewed,senderBundleRoles]
  rw [v,r,i] at bundleBound
  refine ⟨_,?_,viewing.sequence (rowReading.sequence (sending.sequence (viewClear.sequence rowClear)))⟩
  omega

end Counting.StackMachine.NetworkVista
