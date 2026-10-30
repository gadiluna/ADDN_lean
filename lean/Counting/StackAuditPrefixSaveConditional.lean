import Counting.StackAuditPrefixSave
import Counting.StackEncodingBranch

namespace Counting.StackMachine.AuditPrefix
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

abbrev saveIfFlat : Routine 50 := branchRoutine 43 saveAnchor (skip 50)

theorem saveIfFlat_executes (store : Store 50) (level : Nat) (flat : Bool)
    (levelAt : store 30=level.bits) (e0 : store 0=[]) (e4 : store 4=[]) (flag : store 43=[flat]) :
    ∃ time ≤ (store 46).length+9*level.size+16,Executes saveIfFlat store time
      (Function.update (Function.update store 43 []) 46
        (if flat then (level+1).bits else store 46)) := by
  let consumed:=Function.update store 43 []
  cases flat with
  | false=>
    have branch:=branch_executes_false (43:Fin 52) saveAnchor (skip 50) store consumed [] 0 flag
      (skip_executes consumed)
    have final : Function.update consumed 46 (store 46)=consumed := by
      have same : consumed 46=store 46 := by simp [consumed]
      rw [←same,Function.update_eq_self]
    refine ⟨1,by omega,?_⟩
    change Executes saveIfFlat store 1 (Function.update consumed 46 (store 46))
    rw [final]
    exact branch
  | true=>
    obtain ⟨time,bound,run⟩:=saveAnchor_executes consumed level
      (by simp [consumed,levelAt]) (by simp [consumed,e0]) (by simp [consumed,e4])
    have branch:=branch_executes_true (43:Fin 52) saveAnchor (skip 50) store _ [] time flag run
    have same : (consumed 46).length=(store 46).length := by simp [consumed]
    rw [same] at bound
    exact ⟨1+time,by omega,branch⟩

end Counting.StackMachine.AuditPrefix
