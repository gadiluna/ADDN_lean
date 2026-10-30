import Counting.StackEncodingBoundedNatural
import Counting.StackRoutineFixedPrefix

/-! Bounded conversion of the optional-parent code to the node-reader's
unary index. The budget is explicit. Even an enormous malformed reference
never causes a loop proportional to its numeric value. A zero parent code
still requires the separate positive-parent guard. -/
namespace Counting.StackMachine.DagValidation
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

def parentIndexRoutine (extra : Nat) (w : CountWorkspace extra) : Routine (extra+9) :=
  sequence (boundedCount extra w) (discardBit (w 1))

def parentIndexStore (extra : Nat) (w : CountWorkspace extra)
    (store : Store (extra+9)) (code : Nat) : Store (extra+9) :=
  Function.update (boundedNaturalResult extra w store code) (w 1)
    (List.replicate (min code (store (w 10)).length-1) true)

theorem parentIndex_executes (extra : Nat) (w : CountWorkspace extra)
    (store : Store (extra+9)) (code : Nat)
    (header : store (w 0)=Encoding.natural.encode code) (unaryEmpty : store (w 1)=[])
    (workEmpty : ∀ i : Fin 11,i∈({2,3,4,5,7,8,9}:Finset (Fin 11)) → store (w i)=[]) :
    ∃ time ≤ 64*((store (w 10)).length+(Encoding.natural.encode code).length+1)^3+2,
      Executes (parentIndexRoutine extra w) store time (parentIndexStore extra w store code) := by
  obtain ⟨time,bounded,executed⟩:=boundedNatural_executes extra w store code header unaryEmpty workEmpty
  have removed:=discardBit_executes (w 1) (boundedNaturalResult extra w store code)
  rw [boundedNatural_unary,List.tail_replicate] at removed
  exact ⟨time+1+1,by omega,executed.sequence removed⟩

theorem parentIndex_fits (extra : Nat) (w : CountWorkspace extra)
    (store : Store (extra+9)) (parent : Nat) (fits : parent<(store (w 10)).length) :
    parentIndexStore extra w store (parent+1)=
      Function.update (Function.update (Function.update store (w 1) (List.replicate parent true))
        (w 10) []) (w 6) (true::store (w 6)) := by
  have bound : parent+1≤(store (w 10)).length:=by omega
  simp only [parentIndexStore,boundedNaturalResult,Nat.min_eq_left bound,Nat.add_sub_cancel,
    decide_eq_true bound]
  funext r
  by_cases one : r=w 1
  · subst r;simp [w.injective.eq_iff]
  · simp [Function.update_apply,one]

theorem parentIndex_bounded (extra : Nat) (w : CountWorkspace extra)
    (store : Store (extra+9)) (code : Nat) :
    (parentIndexStore extra w store code (w 1)).length ≤ (store (w 10)).length := by
  simp only [parentIndexStore,Function.update_self,List.length_replicate]
  omega

end Counting.StackMachine.DagValidation
