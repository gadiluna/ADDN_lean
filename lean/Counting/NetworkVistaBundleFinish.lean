import Counting.StackEmitNatural
import Counting.StackRoutineBasic
import Counting.EncodingDag

namespace Counting.StackMachine.NetworkVista
open Routine
set_option backward.isDefEq.respectTransparency false

def bundleHeaderRoles : PowerWorkspace 35 := ⟨![25,27,28,29,30],by decide⟩

def finishBundles : Routine 38 := sequence (ofProgram (ListPrograms.reverseProgram 38 24 27))
  (sequence (emitNatural 35 bundleHeaderRoles) (clear 25))

/-- Finalize the compact bundle list by reversing the output once and
computing its binary length header from the measured number of senders. -/
theorem finishBundles_executes (store:Store 38) (messages:List (Executable.Vista×Nat))
    (stream:store 24=(Encoding.sequence (Encoding.product Encoding.vista Encoding.natural) messages).reverse)
    (count:store 25=List.replicate messages.length true)
    (empty:∀r:Fin 40,r∈({27,28,29,30}:Finset (Fin 40)) → store r=[]) :
    ∃time ≤ 30*((store 24).length+(store 25).length+1)^2,
      Executes finishBundles store time
        (Function.update (Function.update (Function.update store 24 []) 25 [])
          27 ((Encoding.list (Encoding.product Encoding.vista Encoding.natural)).encode messages)) := by
  let code:=Encoding.sequence (Encoding.product Encoding.vista Encoding.natural) messages
  have reversing:=reverse_executes 38 (24:Fin 40) 27 (by decide) store
  rw [stream,empty 27 (by decide),List.append_nil,List.reverse_reverse,List.length_reverse] at reversing
  let reversed:=Function.update (Function.update store 24 []) 27 code
  obtain ⟨headerTime,headerBound,framing⟩:=emitNatural_executes 35 bundleHeaderRoles reversed
    (by simp [bundleHeaderRoles,reversed,empty 28 (by decide)])
    (by simp [bundleHeaderRoles,reversed,empty 29 (by decide)])
    (by simp [bundleHeaderRoles,reversed,empty 30 (by decide)])
  have countAt:(reversed (bundleHeaderRoles 0)).length=messages.length:=by simp [bundleHeaderRoles,reversed,count]
  have outputAt:reversed (bundleHeaderRoles 1)=code:=by simp [bundleHeaderRoles,reversed]
  rw [countAt,outputAt] at framing
  rw [countAt] at headerBound
  let framed:=Function.update reversed 27 ((Encoding.list (Encoding.product Encoding.vista Encoding.natural)).encode messages)
  have framing':Executes (emitNatural 35 bundleHeaderRoles) reversed headerTime framed:=framing
  have clearing:=clear_executes (25:Fin 40) framed
  rw [show framed 25=List.replicate messages.length true by simp [framed,reversed,count],List.length_replicate] at clearing
  have final:Function.update framed 25 []=
      Function.update (Function.update (Function.update store 24 []) 25 [])
        27 ((Encoding.list (Encoding.product Encoding.vista Encoding.natural)).encode messages):=by
    simp only [framed,reversed,Function.update_idem]
    exact Function.update_comm (by decide : (27:Fin 40)≠25) _ _ _
  rw [final] at clearing
  refine ⟨_,?_,reversing.sequence (framing'.sequence clearing)⟩
  rw [stream,count,List.length_reverse,List.length_replicate]
  change 2*code.length+1+1+(headerTime+1+(messages.length+1))≤30*(code.length+messages.length+1)^2
  nlinarith only [headerBound,Nat.zero_le code.length,Nat.zero_le messages.length]

end Counting.StackMachine.NetworkVista
