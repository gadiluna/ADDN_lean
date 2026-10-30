import Counting.EncodingSigned
import Counting.StackComparePreserving
import Counting.StackNormalize
import Counting.StackRoutineBasic

namespace Counting.StackMachine.RationalArithmetic
open Routine

/-- Equality of canonical rational encodings is exactly rational equality;
the concrete string comparison preserves both operands and all scratch. -/
theorem rationalEquality_executes (extra : Nat) (roles : Fin 6 ↪ Fin (extra+6))
    (store : Fin (extra+6) → List Bool) (left right : Rat)
    (leftValue : store (roles 0)=Encoding.rational.encode left)
    (rightValue : store (roles 1)=Encoding.rational.encode right)
    (leftEmpty : store (roles 3)=[]) (rightEmpty : store (roles 4)=[])
    (workEmpty : store (roles 5)=[]) :
    Executes (Compare.preservingEquality extra roles) store
      (Compare.preservingCost (Encoding.rational.encode left) (Encoding.rational.encode right))
      (Function.update store (roles 2) (decide (left=right)::store (roles 2))) := by
  have compared := Compare.preservingEquality_executes extra roles store leftEmpty rightEmpty workEmpty
  simpa only [leftValue,rightValue,Encoding.rational_injective.eq_iff] using compared

theorem rationalEquality_cost (left right : Rat) :
    Compare.preservingCost (Encoding.rational.encode left) (Encoding.rational.encode right) ≤
      12*(left.num.natAbs.size+left.den.size+right.num.natAbs.size+right.den.size)+47 := by
  have bounded := Compare.preservingCost_le (Encoding.rational.encode left) (Encoding.rational.encode right)
  rw [Encoding.rational_length,Encoding.rational_length] at bounded
  omega

theorem rational_nat_encode (value : Nat) :
    Encoding.rational.encode (value:Rat) =
      false::(Encoding.natural.encode value++Encoding.natural.encode 1) := by
  simp [Encoding.rational_encode,Encoding.integer_encode,Encoding.negative]

/-- Convert a raw little-endian natural payload to the existing canonical
rational codec. Source is consumed, suffix on output and scratch preserved. -/
def castNatural (extra : Nat) (source target temporary : Fin (extra+3)) : Routine (extra+1) :=
  sequence (prepend target (Encoding.natural.encode 1))
    (sequence (Normalize.formatRoutine extra source target temporary) (pushBit target false))

theorem castNatural_executes (extra : Nat) (source target temporary : Fin (extra+3))
    (distinct : source ≠ target) (sourceTemp : source ≠ temporary) (targetTemp : target ≠ temporary)
    (store : Fin (extra+3) → List Bool) (empty : store temporary=[]) :
    Executes (castNatural extra source target temporary) store (Normalize.formatCost (store source)+9)
      (Function.update (Function.update store source []) target
        (Encoding.rational.encode (Encoding.value (store source):Rat)++store target)) := by
  let middle := Function.update store target (Encoding.natural.encode 1++store target)
  have header := prepend_executes target (Encoding.natural.encode 1) store
  change Executes (prepend target (Encoding.natural.encode 1)) store 6 middle at header
  have formatted := Normalize.format_executes extra source target temporary distinct sourceTemp targetTemp middle
    (by simp [middle,Function.update_of_ne targetTemp.symm,empty])
  have middleSource : middle source=store source := by simp [middle,Function.update_of_ne distinct]
  have middleTarget : middle target=Encoding.natural.encode 1++store target := by simp [middle]
  rw [middleSource,middleTarget] at formatted
  let payload := Encoding.natural.encode (Encoding.value (store source))++Encoding.natural.encode 1++store target
  let finish := Function.update (Function.update store source []) target payload
  have formattedStore : Function.update (Function.update middle source []) target
      (Encoding.natural.encode (Encoding.value (store source))++(Encoding.natural.encode 1++store target)) = finish := by
    funext r
    by_cases atSource : r=source
    · subst r; simp [finish,middle,distinct]
    · by_cases atTarget : r=target
      · subst r; simp [finish,payload,List.append_assoc]
      · simp [finish,middle,Function.update_of_ne,atSource,atTarget]
  rw [formattedStore] at formatted
  have sign := pushBit_executes target false finish
  have finalStore : Function.update finish target (false::finish target) =
      Function.update (Function.update store source []) target
        (Encoding.rational.encode (Encoding.value (store source):Rat)++store target) := by
    simp only [finish,Function.update_self,Function.update_idem,rational_nat_encode,List.cons_append]
    rfl
  rw [finalStore] at sign
  have combined := header.sequence (formatted.sequence sign)
  simpa only [castNatural,show 6+1+(Normalize.formatCost (store source)+1+1)=
    Normalize.formatCost (store source)+9 by omega] using combined

theorem castNatural_cost (payload : List Bool) : Normalize.formatCost payload+9 ≤ 5*payload.length+13 := by
  have := Normalize.formatCost_le payload
  omega

end Counting.StackMachine.RationalArithmetic
