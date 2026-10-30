import Counting.ExternalCoefficientEmit

namespace Counting.External.CoefficientMachine
open StackMachine StackMachine.Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

def rowScratch : List (Fin 64) := tripleScratch++[56]
def writeCoefficientRow (extra : Nat) (w : Workspace extra) : Routine (extra+62) :=
  sequence (coefficientTriple extra w) (emitCoefficient extra w)
def rowCost (sourceLength universeLength baseLength highLength sumLimit : Nat) :=
  tripleCost sourceLength universeLength baseLength highLength sumLimit+9*sumLimit+9

theorem writeCoefficientRow_executes (extra : Nat) (w : Workspace extra) (store : Fin (extra+64) → List Bool)
    (base high : Nat) (row : List Nat) (sumLimit : Nat) (accepted : Bool) (suffix tail : List Bool)
    (source : store (w 0)=(Encoding.list Encoding.natural).encode row++suffix) (length : row.length=3)
    (status : store (w 1)=accepted::tail) (baseInput : store (w 52)=base.bits) (highInput : store (w 54)=high.bits)
    (sumSize : (high+powers base row).bits.length ≤ sumLimit)
    (fits : ∀ e∈row,e ≤ (store (w 17)).length) (empty : ∀ i∈rowScratch,store (w i)=[]) :
    ∃ time ≤ rowCost (store (w 0)).length (store (w 17)).length base.bits.length high.bits.length sumLimit,
      Executes (writeCoefficientRow extra w) store time
        (Function.update (Function.update store (w 0) suffix) (w 36)
          ((Encoding.natural.encode (high+powers base row)).reverse++store (w 36))) := by
  obtain ⟨a,b,c,rfl⟩:=List.length_eq_three.mp length
  obtain ⟨tripleTime,tripleBound,tripling⟩:=coefficientTriple_executes extra w store base high a b c sumLimit accepted suffix tail
    source status baseInput highInput sumSize fits (fun i member=>empty i (List.mem_append_left _ member))
  let value:=high+powers base [a,b,c]
  let computed:=Function.update (Function.update store (w 0) suffix) (w 55) value.bits
  have emitting:=emitCoefficient_executes extra w computed value (by simp [computed])
    (by simp [computed,w.injective.eq_iff,empty,rowScratch])
    (by simp [computed,w.injective.eq_iff,empty,rowScratch,tripleScratch,atomScratch])
  have outputAt : computed (w 36)=store (w 36) := by simp [computed,w.injective.eq_iff]
  rw [outputAt] at emitting
  have final : Function.update (Function.update computed (w 55) []) (w 36)
      ((Encoding.natural.encode value).reverse++store (w 36))=
      Function.update (Function.update store (w 0) suffix) (w 36)
      ((Encoding.natural.encode value).reverse++store (w 36)) := by
    funext r
    by_cases e55 : r=w 55
    · subst r;simp [w.injective.eq_iff,empty,rowScratch,tripleScratch]
    · simp [computed,Function.update_apply,e55]
  rw [final] at emitting
  have valueBound : value.bits.length ≤ sumLimit := sumSize
  exact ⟨tripleTime+1+(9*value.bits.length+8),by unfold rowCost;omega,tripling.sequence emitting⟩

end Counting.External.CoefficientMachine
