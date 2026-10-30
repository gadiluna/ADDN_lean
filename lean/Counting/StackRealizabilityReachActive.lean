import Counting.StackRealizabilityReachImplication

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def activeScanRoles : Fin 4 ↪ Fin 7:=⟨![4,1,5,3],by decide⟩
def activeScan : Routine 5:=mapRegisters activeScanRoles (forEach 2 implicationItem)

theorem activeScan_executes (store : Store 5) (counter : List Bool) (counted : store 5=counter)
    (value : Bool) (tail : List Bool) (accumulated : store 3=value::tail) :
    Executes activeScan store (6*counter.length+1)
      (Function.update (Function.update (Function.update (Function.update store 5 [])
        4 ((store 4).drop counter.length)) 1 ((store 1).drop counter.length))
        3 (implicationFold counter.length (store 4) (store 1) value::tail)):=by
  let original:Store 2:=store ∘ activeScanRoles
  have ran:=implicationLoop_executes original counter counted value tail accumulated
  apply relocate_executes_frame (forEach 2 implicationItem) activeScanRoles store _ original
    (implicationLoopStore original counter.length value tail) _ rfl _ _ ran
  · intro r
    fin_cases r <;> simp [original,activeScanRoles,implicationLoopStore]
  · intro r outside
    have n1 : r≠1:=by intro same;subst r;exact outside 1 rfl
    have n3 : r≠3:=by intro same;subst r;exact outside 3 rfl
    have n4 : r≠4:=by intro same;subst r;exact outside 0 rfl
    have n5 : r≠5:=by intro same;subst r;exact outside 2 rfl
    simp [n1,n3,n4,n5]

/-- Preserve the active mask and width; consume the first `width` seen bits
and accumulate every implication `active[i] → seen[i]`. -/
def activeCheck : Routine 5:=sequence (ofProgram (ListPrograms.copyProgram 4 0 4 6))
  (sequence (ofProgram (ListPrograms.copyProgram 4 2 5 6))
    (sequence activeScan (clear 4)))

theorem activeCheck_executes (store : Store 5) (value : Bool) (tail : List Bool)
    (accumulated : store 3=value::tail) (e4 : store 4=[]) (e5 : store 5=[]) (e6 : store 6=[]) :
    ∃ time ≤ 6*(store 0).length+11*(store 2).length+10,
      Executes activeCheck store time (Function.update (Function.update store 1 ((store 1).drop (store 2).length))
        3 (implicationFold (store 2).length (store 0) (store 1) value::tail)):=by
  have first:=copy_executes 4 0 4 6 (by decide) (by decide) (by decide) store e6
  rw [e4,List.append_nil] at first
  let copied:=Function.update store 4 (store 0)
  have second:=copy_executes 4 2 5 6 (by decide) (by decide) (by decide) copied (by simp [copied,e6])
  have widthAt : copied 2=store 2:=by simp [copied]
  have counterAt : copied 5=[]:=by simp [copied,e5]
  rw [widthAt,counterAt,List.append_nil] at second
  let prepared:=Function.update copied 5 (store 2)
  have scanning:=activeScan_executes prepared (store 2) (by simp [prepared]) value tail
    (by simp [prepared,copied,accumulated])
  let scanned:=Function.update (Function.update (Function.update (Function.update prepared 5 [])
    4 ((prepared 4).drop (store 2).length)) 1 ((prepared 1).drop (store 2).length))
    3 (implicationFold (store 2).length (prepared 4) (prepared 1) value::tail)
  have clearing:=clear_executes (4:Fin 7) scanned
  have activeAt : scanned 4=(store 0).drop (store 2).length:=by simp [scanned,prepared,copied]
  rw [activeAt] at clearing
  have final : Function.update scanned 4 []=
      Function.update (Function.update store 1 ((store 1).drop (store 2).length))
        3 (implicationFold (store 2).length (store 0) (store 1) value::tail):=by
    funext r
    fin_cases r <;> simp [scanned,prepared,copied,e4,e5]
  rw [final] at clearing
  have remaining : ((store 0).drop (store 2).length).length ≤ (store 0).length:=by simp
  exact ⟨_,by omega,first.sequence (second.sequence (scanning.sequence clearing))⟩

end Counting.StackMachine.RealizabilityCheck
