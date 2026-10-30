import Counting.StackRoutineLists

namespace Counting.StackMachine.Routine
set_option backward.isDefEq.respectTransparency false

/-- Source, destination, empty copied buffer, empty copy scratch. -/
def copyReverse (extra : Nat) (w : Fin 4 ↪ Fin (extra+4)) : Routine (extra+2) :=
  sequence (ofProgram (ListPrograms.copyProgram (extra+1) (w 0) (w 2) (w 3)))
    (ofProgram (ListPrograms.reverseProgram (extra+2) (w 2) (w 1)))

theorem copyReverse_executes (extra : Nat) (w : Fin 4 ↪ Fin (extra+4))
    (store : Fin (extra+4) → List Bool) (e2 : store (w 2)=[]) (e3 : store (w 3)=[]) :
    Executes (copyReverse extra w) store (7*(store (w 0)).length+4)
      (Function.update store (w 1) ((store (w 0)).reverse++store (w 1))) := by
  have ne (i j : Fin 4) (different : i≠j) : w i≠w j := fun same => different (w.injective same)
  let copied := Function.update store (w 2) (store (w 0))
  have copying : Executes (ofProgram (ListPrograms.copyProgram (extra+1) (w 0) (w 2) (w 3))) store
      (5*(store (w 0)).length+2) copied := by
    simpa only [e2,List.append_nil,copied] using copy_executes (extra+1) (w 0) (w 2) (w 3)
      (ne 0 2 (by decide)) (ne 0 3 (by decide)) (ne 2 3 (by decide)) store e3
  have reversing := reverse_executes (extra+2) (w 2) (w 1) (ne 2 1 (by decide)) copied
  have source : copied (w 2)=store (w 0) := by simp [copied]
  have target : copied (w 1)=store (w 1) := by simp [copied,w.injective.eq_iff]
  rw [source,target] at reversing
  have restored : Function.update (Function.update copied (w 2) []) (w 1)
      ((store (w 0)).reverse++store (w 1))=
      Function.update store (w 1) ((store (w 0)).reverse++store (w 1)) := by
    simp only [copied,Function.update_idem,←e2,Function.update_eq_self]
  rw [restored] at reversing
  convert copying.sequence reversing using 1 <;> first | rfl | omega

end Counting.StackMachine.Routine
