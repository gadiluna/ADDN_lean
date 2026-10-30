import Counting.StackRealizabilityAccumulate

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false

def preservingSumRoles {extra : Nat} (roles : Fin 5 ↪ Fin (extra+5)) : Fin 4 ↪ Fin (extra+5) where
  toFun i:=roles (![0,2,3,4] i)
  inj':=by
    intro a b same
    have selected:=roles.injective same
    fin_cases a <;> fin_cases b <;> simp_all

/-- Add the second magnitude into the first while preserving the operand
and restoring three reusable scratch registers. -/
def preservingSum (extra : Nat) (roles : Fin 5 ↪ Fin (extra+5)) : Routine (extra+3):=
  sequence (ofProgram (ListPrograms.copyProgram (extra+2) (roles 1) (roles 2) (roles 4)))
    (accumulateAt (preservingSumRoles roles))

theorem preservingSum_executes (extra : Nat) (roles : Fin 5 ↪ Fin (extra+5))
    (store : Store (extra+3)) (e2 : store (roles 2)=[]) (e3 : store (roles 3)=[]) (e4 : store (roles 4)=[]) :
    ∃ time ≤ 30*((store (roles 0)).length+(store (roles 1)).length+1),
      Executes (preservingSum extra roles) store time
        (Function.update store (roles 0)
          (Encoding.value (store (roles 0))+Encoding.value (store (roles 1))).bits):=by
  have ne (i j : Fin 5) (different : i≠j) : roles i≠roles j:=fun same=>different (roles.injective same)
  have copying:=copy_executes (extra+2) (roles 1) (roles 2) (roles 4)
    (ne 1 2 (by decide)) (ne 1 4 (by decide)) (ne 2 4 (by decide)) store e4
  rw [e2,List.append_nil] at copying
  let copied:=Function.update store (roles 2) (store (roles 1))
  obtain ⟨addTime,addBound,adding⟩:=accumulateAt_executes (preservingSumRoles roles) copied
    (by simp [preservingSumRoles,copied,roles.injective.eq_iff,e3])
    (by simp [preservingSumRoles,copied,roles.injective.eq_iff,e4])
  have first : copied (preservingSumRoles roles 0)=store (roles 0):=by
    simp [preservingSumRoles,copied,roles.injective.eq_iff]
  have second : copied (preservingSumRoles roles 1)=store (roles 1):=by simp [preservingSumRoles,copied]
  rw [first,second] at addBound adding
  change Executes (accumulateAt (preservingSumRoles roles)) copied addTime
    (Function.update (Function.update copied (roles 0)
      (Encoding.value (store (roles 0))+Encoding.value (store (roles 1))).bits) (roles 2) []) at adding
  have final : Function.update (Function.update copied (roles 0)
      (Encoding.value (store (roles 0))+Encoding.value (store (roles 1))).bits) (roles 2) []=
      Function.update store (roles 0)
        (Encoding.value (store (roles 0))+Encoding.value (store (roles 1))).bits:=by
    funext r
    by_cases r0 : r=roles 0 <;> by_cases r2 : r=roles 2 <;>
      simp [copied,r0,r2,roles.injective.eq_iff,e2]
  rw [final] at adding
  exact ⟨_,by omega,copying.sequence adding⟩

end Counting.StackMachine.RealizabilityCheck
