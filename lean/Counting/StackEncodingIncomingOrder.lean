import Counting.StackEncodingGuards

namespace Counting.StackMachine.EncodingPrograms
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def dropFlag (extra : Nat) (flag : Fin (extra+2)) : Routine extra :=
  branchRoutine flag (skip extra) (skip extra)

theorem dropFlag_executes (extra : Nat) (flag : Fin (extra+2)) (store : Store extra)
    (bit : Bool) (tail : List Bool) (status : store flag=bit::tail) :
    Executes (dropFlag extra flag) store 1 (Function.update store flag tail) := by
  have body:=skip_executes (Function.update store flag tail)
  cases bit with
  | false => exact branch_executes_false flag _ _ store _ tail 0 status body
  | true => exact branch_executes_true flag _ _ store _ tail 0 status body

/-- On the first item discard the comparison; subsequently negate it. -/
def orderFlag (extra : Nat) (first status : Fin (extra+2)) : Routine extra :=
  branchRoutine first (sequence (dropFlag extra status) (pushBit status true)) (negateFlag extra status)

theorem orderFlag_executes (extra : Nat) (first status : Fin (extra+2)) (distinct : first≠status)
    (store : Store extra) (isFirst compared : Bool) (firstTail tail : List Bool)
    (firstValue : store first=isFirst::firstTail) (statusValue : store status=compared::tail) :
    ∃ time ≤ 4, Executes (orderFlag extra first status) store time
      (Function.update (Function.update store first firstTail) status ((isFirst || !compared)::tail)) := by
  let popped:=Function.update store first firstTail
  have statusPopped : popped status=compared::tail := by simpa [popped,Ne.symm distinct] using statusValue
  cases isFirst with
  | false =>
    have body:=negateFlag_executes extra status popped compared tail statusPopped
    exact ⟨3,by omega,branch_executes_false first _ _ store _ firstTail 2 firstValue body⟩
  | true =>
    have dropped:=dropFlag_executes extra status popped compared tail statusPopped
    have pushed:=pushBit_executes status true (Function.update popped status tail)
    simp only [Function.update_self,Function.update_idem] at pushed
    have body:=dropped.sequence pushed
    exact ⟨4,le_rfl,branch_executes_true first _ _ store _ firstTail 3 firstValue body⟩

def incomingOrderRoles (extra : Nat) (w : Fin 7 ↪ Fin (extra+7)) : Fin 6 ↪ Fin (extra+7) :=
  ⟨fun i=>w ⟨i.val,by omega⟩,fun a b h=>Fin.ext (congrArg (fun i : Fin 7=>i.val) (w.injective h))⟩

/-- Roles: current, previous, status, comparison scratch ×3, first-item bit. -/
def incomingOrder (extra : Nat) (w : Fin 7 ↪ Fin (extra+7)) : Routine (extra+5) :=
  sequence (Binary.preservingComparison (extra+1) (incomingOrderRoles extra w))
    (sequence (orderFlag (extra+5) (w 6) (w 2))
      (sequence (ofProgram (combineFlagsProgram (extra+5) (w 2))) (pushBit (w 6) false)))

theorem incomingOrder_executes (extra : Nat) (w : Fin 7 ↪ Fin (extra+7))
    (store : Store (extra+5)) (accepted first : Bool) (tail firstTail : List Bool)
    (status : store (w 2)=accepted::tail) (firstStatus : store (w 6)=first::firstTail)
    (a : store (w 3)=[]) (b : store (w 4)=[]) (c : store (w 5)=[]) :
    ∃ time ≤ 7*((store (w 0)).length+(store (w 1)).length)+20,
      Executes (incomingOrder extra w) store time
        (Function.update (Function.update store (w 2)
          ((accepted && (first || !Binary.compareBits true (store (w 0)) (store (w 1))))::tail))
          (w 6) (false::firstTail)) := by
  have ne (i j : Fin 7) (h : i≠j) : w i≠w j := fun eq=>h (w.injective eq)
  let cmp:=Binary.compareBits true (store (w 0)) (store (w 1))
  let s1:=Function.update store (w 2) (cmp::store (w 2))
  have r1 : Executes (Binary.preservingComparison (extra+1) (incomingOrderRoles extra w)) store
      (Binary.preservingCompareCost (store (w 0)) (store (w 1))) s1 := by
    exact Binary.preservingComparison_executes (extra+1) (incomingOrderRoles extra w) store a b c
  obtain ⟨t2,b2,r2⟩:=orderFlag_executes (extra+5) (w 6) (w 2) (ne 6 2 (by decide))
    s1 first cmp firstTail (store (w 2))
    (by simpa [s1,w.injective.eq_iff] using firstStatus) (by simp [s1])
  let s2:=Function.update (Function.update s1 (w 6) firstTail) (w 2) ((first || !cmp)::store (w 2))
  have r3:=combineFlags_executes (extra+5) (w 2) s2 accepted (first || !cmp) tail (by simp [s2,status])
  let s3:=Function.update s2 (w 2) ((accepted && (first || !cmp))::tail)
  have r4:=pushBit_executes (w 6) false s3
  have final : Function.update s3 (w 6) (false::s3 (w 6))=
      Function.update (Function.update store (w 2) ((accepted && (first || !cmp))::tail))
        (w 6) (false::firstTail) := by
    funext r
    by_cases h : r=w 6
    · subst r; simp [s3,s2,w.injective.eq_iff]
    · by_cases j : r=w 2 <;> simp [s3,s2,s1,h,j]
  rw [final] at r4
  have composed:=r1.sequence (r2.sequence (r3.sequence r4))
  refine ⟨_,?_,composed⟩
  have bound:=Binary.preservingCompareCost_le (store (w 0)) (store (w 1))
  omega

end Counting.StackMachine.EncodingPrograms
