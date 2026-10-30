import Counting.StackRoutineLists
import Counting.StackRoutineMove
import Counting.StackRoutineBasic
import Counting.EncodingBinary

namespace Counting.StackMachine.AuditPropagation
open Routine
set_option backward.isDefEq.respectTransparency false

abbrev prepareDown : Routine 42 := sequence (clear 18)
  (sequence (clear 36) (sequence (ofProgram (ListPrograms.copyProgram 41 40 36 43))
    (sequence (ofProgram (ListPrograms.copyProgram 41 42 22 43))
      (sequence (clear 30) (move 41 41 39 43)))))

def downSetupStore (store : Store 42) (anchor nodes : Nat) : Store 42 :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update store 18 []) 36 (List.replicate nodes true)) 22 anchor.bits) 30 []) 41 []) 39
      (List.replicate anchor true)

/-- Reuse registers only after explicitly discarding the unused anchor
coordinates and traversal index. Every copy and movement is charged. -/
theorem prepareDown_executes (store : Store 42) (anchor nodes : Nat)
    (oldIndex : (store 18).length=nodes) (count : store 40=List.replicate nodes true)
    (parameter : store 42=anchor.bits) (query : store 30=anchor.bits)
    (rounds : store 41=List.replicate anchor true)
    (e22 : store 22=[]) (e39 : store 39=[]) (e43 : store 43=[]) :
    Executes prepareDown store (6*nodes+(store 36).length+6*anchor.size+6*anchor+16)
      (downSetupStore store anchor nodes) := by
  have a := clear_executes (18:Fin 44) store
  rw [oldIndex] at a
  let first := Function.update store 18 []
  have b := clear_executes (36:Fin 44) first
  have inputAt : first 36=store 36 := by simp [first]
  rw [inputAt] at b
  let cleared := Function.update first 36 []
  have c := copy_executes 41 (40:Fin 44) 36 43 (by decide) (by decide) (by decide) cleared
    (by simp [cleared,first,e43])
  have countAt : cleared 40=List.replicate nodes true := by simp [cleared,first,count]
  have emptyAt : cleared 36=[] := by simp [cleared]
  rw [countAt,emptyAt,List.append_nil,List.length_replicate] at c
  let counted := Function.update first 36 (List.replicate nodes true)
  have cs : Function.update cleared 36 (List.replicate nodes true)=counted := by simp only [cleared,Function.update_idem,counted]
  rw [cs] at c
  have d := copy_executes 41 (42:Fin 44) 22 43 (by decide) (by decide) (by decide) counted
    (by simp [counted,first,e43])
  have anchorAt : counted 42=anchor.bits := by simp [counted,first,parameter]
  have targetAt : counted 22=[] := by simp [counted,first,e22]
  rw [anchorAt,targetAt,List.append_nil,Encoding.bits_length] at d
  let leveled := Function.update counted 22 anchor.bits
  have e := clear_executes (30:Fin 44) leveled
  have queryAt : leveled 30=anchor.bits := by simp [leveled,counted,first,query]
  rw [queryAt,Encoding.bits_length] at e
  let ready := Function.update leveled 30 []
  have f := move_executes 41 (41:Fin 44) 39 43 (by decide) (by decide) (by decide) ready
    (by simp [ready,leveled,counted,first,e43])
  have sourceAt : ready 41=List.replicate anchor true := by simp [ready,leveled,counted,first,rounds]
  have targetEmpty : ready 39=[] := by simp [ready,leveled,counted,first,e39]
  rw [sourceAt,targetEmpty,List.append_nil,List.length_replicate] at f
  have fs : Function.update (Function.update ready 39 (List.replicate anchor true)) 41 []=
      downSetupStore store anchor nodes := by
    funext i
    by_cases i39 : i=39 <;> by_cases i41 : i=41 <;>
      simp [downSetupStore,ready,leveled,counted,first,i39,i41]
  rw [fs] at f
  convert a.sequence (b.sequence (c.sequence (d.sequence (e.sequence f)))) using 1
  omega

end Counting.StackMachine.AuditPropagation
