import Counting.StackEmitSyntax
import Counting.StackRoutineFixedPrefix

namespace Counting.StackMachine.Routine

/-- Add a compile-time offset temporarily to the unary identifier, emit its
literal, and restore the original source counter. -/
def emitOffsetLiteral (extra : Nat) (w : PowerWorkspace extra) (offset : Nat) (positive : Bool) : Routine (extra+3) :=
  sequence (prepend (w 0) (List.replicate offset true))
    (sequence (emitLiteral extra w positive) (discard (w 0) offset))

def offsetLiteralCoefficient (offset : Nat) : Nat := 22*(offset+1)^2+4*offset+2

theorem emitOffsetLiteral_executes (extra : Nat) (w : PowerWorkspace extra) (offset : Nat) (positive : Bool)
    (store : Fin (extra+5) → List Bool) (counterEmpty : store (w 2) = [])
    (binaryEmpty : store (w 3) = []) (workEmpty : store (w 4) = []) :
    ∃ transitions ≤ offsetLiteralCoefficient offset*((store (w 0)).length+1)^2,
      Executes (emitOffsetLiteral extra w offset positive) store transitions
        (Function.update store (w 1)
          ((Encoding.product Encoding.natural Encoding.boolean).encode ((store (w 0)).length+offset,positive)++store (w 1))) := by
  let added := Function.update store (w 0) (List.replicate offset true++store (w 0))
  have add : Executes (prepend (w 0) (List.replicate offset true)) store (2*offset) added := by
    simpa only [List.length_replicate,added] using prepend_executes (w 0) (List.replicate offset true) store
  obtain ⟨emitTime,emitBound,emitted⟩ := emitLiteral_executes extra w positive added
    (by simp [added,w.injective.eq_iff,counterEmpty])
    (by simp [added,w.injective.eq_iff,binaryEmpty])
    (by simp [added,w.injective.eq_iff,workEmpty])
  let afterEmit := Function.update added (w 1)
    ((Encoding.product Encoding.natural Encoding.boolean).encode ((added (w 0)).length,positive)++added (w 1))
  have discarded := discard_executes (w 0) offset afterEmit
  have combined := add.sequence (emitted.sequence discarded)
  refine ⟨2*offset+1+(emitTime+1+2*offset),?_,?_⟩
  · simp only [added,Function.update_self,List.length_append,List.length_replicate] at emitBound
    have baseBound : offset+(store (w 0)).length+1 ≤ (offset+1)*((store (w 0)).length+1) := by nlinarith
    have squares := Nat.mul_le_mul_left 22 (Nat.pow_le_pow_left baseBound 2)
    have positiveSquare : 1 ≤ ((store (w 0)).length+1)^2 := Nat.one_le_pow 2 _ (by omega)
    have constant := Nat.mul_le_mul_left (4*offset+2) positiveSquare
    unfold offsetLiteralCoefficient
    nlinarith
  · have restored : Function.update afterEmit (w 0) ((afterEmit (w 0)).drop offset) =
        Function.update store (w 1)
          ((Encoding.product Encoding.natural Encoding.boolean).encode ((store (w 0)).length+offset,positive)++store (w 1)) := by
      funext register
      by_cases source : register = w 0
      · subst register
        simp [afterEmit,added,w.injective.eq_iff]
      · by_cases target : register = w 1
        · subst register
          simp [afterEmit,added,w.injective.eq_iff,Nat.add_comm]
        · simp [afterEmit,added,source,target]
    rw [restored] at combined
    exact combined

end Counting.StackMachine.Routine
