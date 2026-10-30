import Counting.StackBinaryPredecessorPositive
import Counting.StackDagEmptyGuard

namespace Counting.StackMachine.Binary
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

def predecessor (extra : Nat) (w : PredWorkspace extra) : Routine (extra+6) :=
  sequence (DagValidation.emptyFlag (w 0) (w 7))
    (branchRoutine (w 7) (skip (extra+6)) (positivePredecessor extra w))

/-- Saturating predecessor of a canonical binary natural. The source and
every external register survive; all private registers are restored. The
bound depends on bit length, without expanding the binary value in unary. -/
theorem predecessor_executes (extra : Nat) (w : PredWorkspace extra)
    (store : Fin (extra+8)→List Bool) (n : Nat)
    (source : store (w 0)=n.bits)
    (empty : ∀ i∈([1,2,3,4,5,6,7] : List (Fin 8)),store (w i)=[]) :
    ∃ time ≤ 60*(n.size+1),
      Executes (predecessor extra w) store time (Function.update store (w 1) (n-1).bits) := by
  have nil_iff : n.bits=[] ↔ n=0 := by
    constructor
    · intro equal
      have values := congrArg Encoding.value equal
      simpa only [Encoding.value_bits,Encoding.value] using values
    · rintro rfl;rfl
  have flagging := DagValidation.emptyFlag_executes (w 0) (w 7) store
  let checked := Function.update store (w 7) [decide (n=0)]
  have flagAs : Executes (DagValidation.emptyFlag (w 0) (w 7)) store
      (DagValidation.emptyFlagCost n.bits) checked := by
    simpa only [source,empty 7 (by simp),nil_iff,checked] using flagging
  have popped : Function.update checked (w 7) []=store := by
    simp only [checked,Function.update_idem,←empty 7 (by simp),Function.update_eq_self]
  have flagBound : DagValidation.emptyFlagCost n.bits ≤ 3 := by
    unfold DagValidation.emptyFlagCost
    split <;> omega
  by_cases zero : n=0
  · have branching := branch_executes_true (w 7) (skip (extra+6)) (positivePredecessor extra w)
      checked store [] 0 (by simp [checked,zero])
      (by rw [popped];exact skip_executes store)
    have result : Function.update store (w 1) (n-1).bits=store := by
      rw [zero]
      change Function.update store (w 1) []=store
      rw [←empty 1 (by simp),Function.update_eq_self]
    rw [result]
    exact ⟨_,by omega,flagAs.sequence branching⟩
  · obtain ⟨time,bound,executing⟩ := positivePredecessor_executes extra w store n (by omega) source
      (by intro i member;exact empty i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at member ⊢;tauto))
    have branching := branch_executes_false (w 7) (skip (extra+6)) (positivePredecessor extra w)
      checked (Function.update store (w 1) (n-1).bits) [] time (by simp [checked,zero])
      (by rw [popped];exact executing)
    exact ⟨_,by omega,flagAs.sequence branching⟩

end Counting.StackMachine.Binary
