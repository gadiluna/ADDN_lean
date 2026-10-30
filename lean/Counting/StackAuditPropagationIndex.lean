import Counting.StackRoutineUnary
import Counting.StackRoutineLists
import Counting.StackRoutineBasic

namespace Counting.StackMachine.AuditPropagation
open Routine
set_option backward.isDefEq.respectTransparency false

/-- The node index is already a bounded unary traversal counter. This
routine copies it, adds one for the framed-array header and generates the
binary parent query used by the child scan. -/
abbrev prepareNodeIndex : Routine 38 := sequence (ofProgram (ListPrograms.copyProgram 37 18 31 4))
  (sequence (pushBit 31 true)
    (sequence (ofProgram (ListPrograms.copyProgram 37 31 26 4))
      (ofProgram (Unary.toBinaryProgram 37 26 25 4))))

theorem prepareNodeIndex_executes (store : Store 38) (index : Nat)
    (counter : store 18=List.replicate index true)
    (e4 : store 4=[]) (e25 : store 25=[]) (e26 : store 26=[]) (e31 : store 31=[]) :
    ∃ time ≤ 30*(index+1)^2,
      Executes prepareNodeIndex store time
        (Function.update (Function.update store 31 (List.replicate (index+1) true)) 25 (index+1).bits) := by
  have a := copy_executes 37 (18:Fin 40) 31 4 (by decide) (by decide) (by decide) store e4
  rw [counter,e31,List.append_nil,List.length_replicate] at a
  let copied := Function.update store 31 (List.replicate index true)
  have b := pushBit_executes (31:Fin 40) true copied
  have prepared : Function.update copied 31 (true::copied 31)=
      Function.update store 31 (List.replicate (index+1) true) := by simp [copied,List.replicate_succ]
  rw [prepared] at b
  let unary := Function.update store 31 (List.replicate (index+1) true)
  have c := copy_executes 37 (31:Fin 40) 26 4 (by decide) (by decide) (by decide) unary (by simp [unary,e4])
  have unaryAt : unary 31=List.replicate (index+1) true := by simp [unary]
  have emptyAt : unary 26=[] := by simp [unary,e26]
  rw [unaryAt,emptyAt,List.append_nil,List.length_replicate] at c
  let doubled := Function.update unary 26 (List.replicate (index+1) true)
  obtain ⟨time,bounded,d⟩ := toBinary_executes 37 (26:Fin 40) 25 4
    (by decide) (by decide) (by decide) doubled 0 (by simp [doubled,unary,e25]) (by simp [doubled,unary,e4])
  have counterAt : doubled 26=List.replicate (index+1) true := by simp [doubled]
  rw [counterAt,List.length_replicate,Nat.zero_add] at d bounded
  have result : Function.update (Function.update doubled 26 []) 25 (index+1).bits=
      Function.update unary 25 (index+1).bits := by
    simp only [doubled,Function.update_idem]
    rw [←emptyAt,Function.update_eq_self]
  rw [result] at d
  refine ⟨_,?_,a.sequence (b.sequence (c.sequence d))⟩
  nlinarith

end Counting.StackMachine.AuditPropagation
