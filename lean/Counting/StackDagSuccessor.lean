import Counting.StackDagGuards

namespace Counting.StackMachine.DagValidation
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

/-- Roles are old level, new level, status, increment copy, and three
scratch registers. The old level is preserved even when increment carries. -/
def successorRoles (extra : Nat) (w : Fin 7 ↪ Fin (extra+7)) : Fin 6 ↪ Fin (extra+7) where
  toFun i:=w (![3,1,2,4,5,6] i)
  inj':=by
    intro a b equal
    have h:=w.injective equal
    fin_cases a <;> fin_cases b <;> simp_all

def successorGuard (extra : Nat) (w : Fin 7 ↪ Fin (extra+7)) : Routine (extra+5) :=
  sequence (ofProgram (ListPrograms.copyProgram (extra+4) (w 0) (w 3) (w 4)))
    (sequence (incrementRoutine (extra+4) (w 6) (w 3) (w 4))
      (sequence (equalityGuard (extra+1) (successorRoles extra w)) (clear (w 3))))

def successorCost (before after : List Bool) : Nat:=
  (5*before.length+2)+1+((4*Machine.carryLength before+7)+1+
    ((Compare.preservingCost (Machine.increment before) after+4)+1+
      ((Machine.increment before).length+1)))

theorem successorGuard_executes (extra : Nat) (w : Fin 7 ↪ Fin (extra+7))
    (store : Store (extra+5)) (accepted : Bool) (tail : List Bool)
    (flag : store (w 2)=accepted::tail)
    (work : ∀ i : Fin 7,i∈({3,4,5,6}:Finset (Fin 7)) → store (w i)=[]) :
    Executes (successorGuard extra w) store (successorCost (store (w 0)) (store (w 1)))
      (Function.update store (w 2)
        ((accepted && decide (Machine.increment (store (w 0))=store (w 1)))::tail)) := by
  have ne (i j : Fin 7) (h : i≠j) : w i≠w j:=fun equal=>h (w.injective equal)
  have copied:=copy_executes (extra+4) (w 0) (w 3) (w 4) (ne 0 3 (by decide))
    (ne 0 4 (by decide)) (ne 3 4 (by decide)) store (work 4 (by decide))
  rw [work 3 (by decide),List.append_nil] at copied
  let middle:=Function.update store (w 3) (store (w 0))
  have incremented:=increment_executes (extra+4) (w 6) (w 3) (w 4) (ne 6 3 (by decide))
    (ne 6 4 (by decide)) (ne 3 4 (by decide)) middle
    (by simp [middle,w.injective.eq_iff,work 6 (by decide)])
    (by simp [middle,w.injective.eq_iff,work 4 (by decide)])
  simp only [middle,Function.update_self,Function.update_idem] at incremented
  let increased:=Function.update store (w 3) (Machine.increment (store (w 0)))
  have compared:=equalityGuard_executes (extra+1) (successorRoles extra w) increased accepted tail
    (by simp [successorRoles,increased,w.injective.eq_iff,flag])
    (by simp [successorRoles,increased,w.injective.eq_iff,work 4 (by decide)])
    (by simp [successorRoles,increased,w.injective.eq_iff,work 5 (by decide)])
    (by simp [successorRoles,increased,w.injective.eq_iff,work 6 (by decide)])
  change Executes (equalityGuard (extra+1) (successorRoles extra w)) increased
    (Compare.preservingCost (increased (w 3)) (increased (w 1))+4)
    (Function.update increased (w 2)
      ((accepted && decide (increased (w 3)=increased (w 1)))::tail)) at compared
  have value3 : increased (w 3)=Machine.increment (store (w 0)):=by simp [increased]
  have value1 : increased (w 1)=store (w 1):=by simp [increased,w.injective.eq_iff]
  rw [value3,value1] at compared
  let checked:=Function.update increased (w 2)
    ((accepted && decide (Machine.increment (store (w 0))=store (w 1)))::tail)
  have clearing:=clear_executes (w 3) checked
  have clearValue : checked (w 3)=Machine.increment (store (w 0)):=by
    simp [checked,increased,w.injective.eq_iff]
  rw [clearValue] at clearing
  have restored : Function.update checked (w 3) []=
      Function.update store (w 2)
        ((accepted && decide (Machine.increment (store (w 0))=store (w 1)))::tail) := by
    funext r
    by_cases first : r=w 3
    · subst r;simp [w.injective.eq_iff,work 3 (by decide)]
    · simp [checked,increased,Function.update_apply,first]
  rw [restored] at clearing
  exact copied.sequence (incremented.sequence (compared.sequence clearing))

theorem increment_length_le (bits : List Bool) :
    (Machine.increment bits).length ≤ bits.length+1 := by
  induction bits with
  | nil => simp [Machine.increment]
  | cons bit bits ih =>
    cases bit with
    | false => simp [Machine.increment]
    | true => simpa only [Machine.increment,List.length_cons] using Nat.succ_le_succ ih

theorem successorCost_le (before after : List Bool) :
    successorCost before after≤16*before.length+6*after.length+35 := by
  have carry:=Machine.carryLength_le before
  have increment:=increment_length_le before
  have compare:=Compare.preservingCost_le (Machine.increment before) after
  unfold successorCost
  omega

theorem successor_naturals (a b : Nat) :
    decide (Machine.increment a.bits=b.bits)=decide (a+1=b) := by
  rw [Machine.increment_bits]
  simp only [Encoding.bits_injective.eq_iff]

end Counting.StackMachine.DagValidation
