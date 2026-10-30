import Counting.StackEncodingFrame
import Counting.StackRoutineLists
import Counting.StackRoutineBasic
import Counting.EncodingDag

namespace Counting.StackMachine.NetworkVista
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

/-- Append one binary multiplicity bundle to a reversed output stream.
The serialized view is preserved, and the binary count is consumed. -/
def emitBundle : Routine 14 := sequence (ofProgram (ListPrograms.copyProgram 13 0 8 9))
  (sequence (ofProgram (ListPrograms.reverseProgram 14 8 3))
    (sequence (frameRoutine 13 5 8 9)
      (sequence (ofProgram (ListPrograms.reverseProgram 14 8 3)) (pushBit 4 true))))

def emitBundleStore (store:Store 14) : Store 14 :=
  Function.update (Function.update (Function.update store 5 [])
    3 ((store 0++Encoding.frame (store 5)).reverse++store 3)) 4 (true::store 4)

theorem emitBundle_executes (store:Store 14) (e8:store 8=[]) (e9:store 9=[]) :
    Executes emitBundle store (7*(store 0).length+9*(store 5).length+15) (emitBundleStore store) := by
  have copying:=copy_executes 13 (0:Fin 16) 8 9 (by decide) (by decide) (by decide) store e9
  rw [e8,List.append_nil] at copying
  let copied:=Function.update store 8 (store 0)
  have reversing:=reverse_executes 14 (8:Fin 16) 3 (by decide) copied
  rw [show copied 8=store 0 by simp [copied],show copied 3=store 3 by simp [copied]] at reversing
  let emittedView:=Function.update (Function.update copied 8 []) 3 ((store 0).reverse++store 3)
  have framing:=frame_executes 13 (5:Fin 16) 8 9 (by decide) (by decide) (by decide) emittedView (by simp [emittedView,copied,e9])
  rw [show emittedView 5=store 5 by simp [emittedView,copied]] at framing
  let framed:=frameResult 13 5 8 9 emittedView
  have finishReverse:=reverse_executes 14 (8:Fin 16) 3 (by decide) framed
  rw [show framed 8=Encoding.frame (store 5) by simp [framed,frameResult,emittedView,copied],
    show framed 3=(store 0).reverse++store 3 by simp [framed,frameResult,emittedView,copied]] at finishReverse
  let reversed:=Function.update (Function.update framed 8 []) 3
    ((Encoding.frame (store 5)).reverse++((store 0).reverse++store 3))
  have counting:=pushBit_executes (4:Fin 16) true reversed
  have final:Function.update reversed 4 (true::reversed 4)=emitBundleStore store:=by
    funext r
    fin_cases r <;> simp [reversed,framed,frameResult,emittedView,copied,emitBundleStore,e8,e9,List.reverse_append,List.append_assoc]
  rw [final] at counting
  have run:=copying.sequence (reversing.sequence (framing.sequence (finishReverse.sequence counting)))
  convert run using 1 <;> first | rfl | (simp only [Encoding.frame_length];omega)

theorem emitBundle_typed (store:Store 14) (e8:store 8=[]) (e9:store 9=[])
    (vista:Executable.Vista) (count:Nat)
    (view:store 0=Encoding.vista.encode vista) (amount:store 5=count.bits) :
    Executes emitBundle store (7*(Encoding.vista.encode vista).length+9*count.size+15)
      (Function.update (Function.update (Function.update store 5 [])
        3 (((Encoding.product Encoding.vista Encoding.natural).encode (vista,count)).reverse++store 3))
        4 (true::store 4)) := by
  simpa only [emitBundleStore,view,amount,Encoding.bits_length,Encoding.product,Encoding.natural]
    using emitBundle_executes store e8 e9

end Counting.StackMachine.NetworkVista
