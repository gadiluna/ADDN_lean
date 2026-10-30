import Counting.ExternalGeneratorCountCore

namespace Counting.External.CookLevin.StackGenerator
open StackMachine StackMachine.Routine

/-- Precompute persistent unary counts before the clause stream consumes
its cell counter. Roles 22 and 23 are reserved for the two outer headers. -/
def generatorCounts (extra : Nat) (w : GeneratorWorkspace extra) (program : Machine.Program) : Routine (extra+30) :=
  sequence (pushBit (w 21) true)
    (sequence (generatorCountCore extra w program)
      (sequence (clear (w 21)) (sequence (pushBit (w 23) true)
        (scaleLength (extra+29) (w 26) (w 22) (w 31) (Cellular.alphabet program)))))

def generatorCountsCost (program : Machine.Program) (cells width capacity : Nat) :=
  generatorCountCoreCost program cells width capacity+8+Cellular.alphabet program*(5*cells+3)

theorem generatorCounts_executes (extra : Nat) (w : GeneratorWorkspace extra) (program : Machine.Program)
    (cells width capacity : Nat) (store : Fin (extra+32) → List Bool)
    (cellsLength : (store (w 26)).length=cells) (widthLength : (store (w 1)).length=width)
    (capacityLength : (store (w 4)).length=capacity)
    (empty : ∀ i ∈ ([21,22,23,24,27,31] : List (Fin 32)), store (w i)=[]) :
    Executes (generatorCounts extra w program) store (generatorCountsCost program cells width capacity)
      (Function.update (Function.update store (w 23) (List.replicate (formulaClauseCount program cells width capacity) true))
        (w 22) (List.replicate (cells*Cellular.alphabet program) true)) := by
  let unitStore := Function.update store (w 21) [true]
  let coreValue := generatorCountCoreValue program cells width capacity
  let coreStore := Function.update unitStore (w 23) (List.replicate coreValue true)
  let cleaned := Function.update store (w 23) (List.replicate coreValue true)
  let complete := Function.update store (w 23) (List.replicate (formulaClauseCount program cells width capacity) true)
  have first : Executes (pushBit (w 21) true) store 1 unitStore := by
    simpa only [unitStore,empty 21 (by simp)] using pushBit_executes (w 21) true store
  have second : Executes (generatorCountCore extra w program) unitStore (generatorCountCoreCost program cells width capacity) coreStore := by
    have run := generatorCountCore_executes extra w program cells width capacity unitStore
      (by simp [unitStore,w.injective.eq_iff,cellsLength])
      (by simp [unitStore,w.injective.eq_iff,widthLength])
      (by simp [unitStore,w.injective.eq_iff,capacityLength])
      (by simp [unitStore])
      (by simp [unitStore,w.injective.eq_iff,empty 24 (by simp)])
      (by simp [unitStore,w.injective.eq_iff,empty 27 (by simp)])
      (by simp [unitStore,w.injective.eq_iff,empty 31 (by simp)])
    simpa [coreStore,unitStore,coreValue,w.injective.eq_iff,empty 23 (by simp)] using run
  have third : Executes (clear (w 21)) coreStore 2 cleaned := by
    have run := clear_executes (w 21) coreStore
    have value : (coreStore (w 21)).length=1 := by simp [coreStore,unitStore,w.injective.eq_iff]
    have restore : Function.update coreStore (w 21) []=cleaned := by
      funext r
      by_cases a : r=w 21
      · subst r; simp [cleaned,w.injective.eq_iff,empty 21 (by simp)]
      · by_cases b : r=w 23 <;> simp [coreStore,unitStore,cleaned,a,b]
    simpa only [value,restore] using run
  have fourth : Executes (pushBit (w 23) true) cleaned 1 complete := by
    have count : formulaClauseCount program cells width capacity=coreValue+1 := rfl
    simpa only [complete,count,cleaned,Function.update_self,Function.update_idem,List.replicate_succ] using
      pushBit_executes (w 23) true cleaned
  have fifth : Executes (scaleLength (extra+29) (w 26) (w 22) (w 31) (Cellular.alphabet program)) complete
      (Cellular.alphabet program*(5*cells+3))
      (Function.update complete (w 22) (List.replicate (cells*Cellular.alphabet program) true)) := by
    have run := scaleLength_executes (extra+29) (w 26) (w 22) (w 31)
      (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (Cellular.alphabet program) complete
      (by simp [complete,w.injective.eq_iff,empty 31 (by simp)])
    simpa [complete,w.injective.eq_iff,cellsLength,empty 22 (by simp),Nat.mul_comm] using run
  have combined := first.sequence (second.sequence (third.sequence (fourth.sequence fifth)))
  simpa only [generatorCounts,generatorCountsCost,show
    1+1+(generatorCountCoreCost program cells width capacity+1+(2+1+(1+1+Cellular.alphabet program*(5*cells+3))))=
      generatorCountCoreCost program cells width capacity+8+Cellular.alphabet program*(5*cells+3) by omega] using combined

end Counting.External.CookLevin.StackGenerator
