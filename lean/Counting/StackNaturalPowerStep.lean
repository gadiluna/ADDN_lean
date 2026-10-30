import Counting.StackNaturalCallRelocate
import Counting.StackRoutineMove

namespace Counting.StackMachine.NaturalPower
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Binary base and accumulator, eleven arithmetic work registers,
a unary iteration counter, and one move scratch register. -/
abbrev Workspace (extra : Nat) := Fin 15 ↪ Fin (extra+15)

def arithmeticPositions : Fin 13 ↪ Fin 15 :=
  ⟨fun i=>⟨i.val,by omega⟩,by intro a b h;exact Fin.ext (congrArg (fun i : Fin 15=>i.val) h)⟩
def Workspace.arithmetic (w : Workspace extra) : Fin 13 ↪ Fin (extra+15) := arithmeticPositions.trans w

def multiplyStep (extra : Nat) (w : Workspace extra) : Routine (extra+13) :=
  sequence (relocate NaturalCall.multiplicationRoutine w.arithmetic)
    (sequence (clear (w 1)) (move (extra+12) (w 2) (w 1) (w 14)))

theorem multiplyStep_executes (extra : Nat) (w : Workspace extra) (store : Fin (extra+15) → List Bool)
    (empty : ∀ i : Fin 15,i≠0 → i≠1 → i≠13 → store (w i)=[]) :
    ∃ time ≤ 100000*((store (w 0)).length+(store (w 1)).length+1)^3,
      Executes (multiplyStep extra w) store time
        (Function.update store (w 1) (Encoding.value (store (w 0))*Encoding.value (store (w 1))).bits) := by
  obtain ⟨callTime,callBound,callRun⟩ := NaturalCall.multiplication_executes (store (w 0)) (store (w 1))
  have restricted : store ∘ w.arithmetic=NaturalCall.file (store (w 0)) (store (w 1)) [] [] [] [] [] := by
    funext i;fin_cases i <;> simp [Workspace.arithmetic,arithmeticPositions,NaturalCall.file,empty]
  have multiplying := NaturalCall.callAt_executes NaturalCall.multiplicationRoutine w.arithmetic store _ _ _ callTime restricted callRun
  let result := (Encoding.value (store (w 0))*Encoding.value (store (w 1))).bits
  let multiplied := Function.update store (w 2) result
  change Executes (relocate NaturalCall.multiplicationRoutine w.arithmetic) store callTime multiplied at multiplying
  have clearing := clear_executes (w 1) multiplied
  have original : multiplied (w 1)=store (w 1) := by simp [multiplied,w.injective.eq_iff]
  rw [original] at clearing
  let cleared := Function.update multiplied (w 1) []
  have moving := move_executes (extra+12) (w 2) (w 1) (w 14)
    (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) cleared
    (by simp [cleared,multiplied,w.injective.eq_iff,empty])
  have source : cleared (w 2)=result := by simp [cleared,multiplied,w.injective.eq_iff]
  have target : cleared (w 1)=[] := by simp [cleared]
  rw [source,target,List.append_nil] at moving
  have final : Function.update (Function.update cleared (w 1) result) (w 2) []=Function.update store (w 1) result := by
    funext r
    by_cases e2 : r=w 2
    · subst r;simp [w.injective.eq_iff,empty]
    · simp [cleared,multiplied,Function.update_apply,e2]
  rw [final] at moving
  refine ⟨callTime+1+((store (w 1)).length+1+1+(6*result.length+4)),?_,multiplying.sequence (clearing.sequence moving)⟩
  have resultBound := NaturalCall.product_bits_length (store (w 0)) (store (w 1))
  have linear : (store (w 0)).length+(store (w 1)).length+1 ≤
      ((store (w 0)).length+(store (w 1)).length+1)^3 := Nat.le_self_pow (by decide) _
  dsimp only [result] at *
  omega

theorem power_bits_length (base : List Bool) (exponent : Nat) :
    (Encoding.value base^exponent).bits.length ≤ exponent*base.length+1 := by
  induction exponent with
  | zero => simp
  | succ exponent ih =>
    have product := NaturalCall.product_bits_length base (Encoding.value base^exponent).bits
    rw [Encoding.value_bits,←pow_succ'] at product
    exact product.trans (by nlinarith)

end Counting.StackMachine.NaturalPower
