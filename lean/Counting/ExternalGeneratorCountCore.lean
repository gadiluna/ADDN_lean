import Counting.ExternalGeneratorWorkspace
import Counting.ExternalFormulaTotalCount
import Counting.StackAddScaledDifference

namespace Counting.External.CookLevin.StackGenerator
open StackMachine StackMachine.Routine

def generatorOrdinarySelection : Fin 6 ↪ Fin 32 := ⟨![1,4,23,24,27,31],by decide⟩
def generatorBinaryCountSelection : Fin 6 ↪ Fin 32 := ⟨![4,21,23,24,27,31],by decide⟩
def generatorTransitionCountSelection : Fin 6 ↪ Fin 32 := ⟨![26,1,23,24,27,31],by decide⟩
def GeneratorWorkspace.ordinaryCountRoles (w : GeneratorWorkspace extra) : PolynomialWorkspace (extra+26) := generatorOrdinarySelection.trans w
def GeneratorWorkspace.binaryCountRoles (w : GeneratorWorkspace extra) : PolynomialWorkspace (extra+26) := generatorBinaryCountSelection.trans w
def GeneratorWorkspace.transitionCountRoles (w : GeneratorWorkspace extra) : PolynomialWorkspace (extra+26) := generatorTransitionCountSelection.trans w

def generatorCountCore (extra : Nat) (w : GeneratorWorkspace extra) (program : Machine.Program) : Routine (extra+30) :=
  sequence (scaleLength (extra+29) (w 26) (w 23) (w 31) (oneHotTemplate (Cellular.alphabet program)).length)
    (sequence (scaleLength (extra+29) (w 4) (w 23) (w 31) (Cellular.alphabet program-3))
      (sequence (addScaledDifference (extra+26) w.ordinaryCountRoles (Cellular.alphabet program-1))
        (sequence (addScaledDifference (extra+26) w.binaryCountRoles (initialBinaryTemplate program).length)
          (addScaledDifference (extra+26) w.transitionCountRoles (transitionClauseCount program)))))

def generatorCountCoreValue (program : Machine.Program) (cells width capacity : Nat) :=
  cells*(oneHotTemplate (Cellular.alphabet program)).length+capacity*(Cellular.alphabet program-3)+
    (width-capacity)*(Cellular.alphabet program-1)+(capacity-1)*(initialBinaryTemplate program).length+
      (cells-width)*transitionClauseCount program

def generatorCountCoreCost (program : Machine.Program) (cells width capacity : Nat) :=
  (oneHotTemplate (Cellular.alphabet program)).length*(5*cells+3)+1+
    ((Cellular.alphabet program-3)*(5*capacity+3)+1+
      (addScaledDifferenceCost width capacity (Cellular.alphabet program-1)+1+
        (addScaledDifferenceCost capacity 1 (initialBinaryTemplate program).length+1+
          addScaledDifferenceCost cells width (transitionClauseCount program))))

theorem generatorCountCore_executes (extra : Nat) (w : GeneratorWorkspace extra) (program : Machine.Program)
    (cells width capacity : Nat) (store : Fin (extra+32) → List Bool)
    (cellsLength : (store (w 26)).length=cells) (widthLength : (store (w 1)).length=width)
    (capacityLength : (store (w 4)).length=capacity) (unitLength : (store (w 21)).length=1)
    (differenceEmpty : store (w 24)=[]) (counterEmpty : store (w 27)=[]) (workEmpty : store (w 31)=[]) :
    Executes (generatorCountCore extra w program) store (generatorCountCoreCost program cells width capacity)
      (Function.update store (w 23)
        (List.replicate (generatorCountCoreValue program cells width capacity) true++store (w 23))) := by
  let a := Cellular.alphabet program
  let h := (oneHotTemplate a).length
  let b := (initialBinaryTemplate program).length
  let d := transitionClauseCount program
  let v₁ := h*cells
  let v₂ := v₁+(a-3)*capacity
  let v₃ := v₂+(a-1)*(width-capacity)
  let v₄ := v₃+b*(capacity-1)
  let v₅ := v₄+d*(cells-width)
  let s₁ := Function.update store (w 23) (List.replicate v₁ true++store (w 23))
  let s₂ := Function.update store (w 23) (List.replicate v₂ true++store (w 23))
  let s₃ := Function.update store (w 23) (List.replicate v₃ true++store (w 23))
  let s₄ := Function.update store (w 23) (List.replicate v₄ true++store (w 23))
  let s₅ := Function.update store (w 23) (List.replicate v₅ true++store (w 23))
  have first : Executes (scaleLength (extra+29) (w 26) (w 23) (w 31) h) store (h*(5*cells+3)) s₁ := by
    simpa only [s₁,v₁,cellsLength] using scaleLength_executes (extra+29) (w 26) (w 23) (w 31)
      (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) h store workEmpty
  have second : Executes (scaleLength (extra+29) (w 4) (w 23) (w 31) (a-3)) s₁ ((a-3)*(5*capacity+3)) s₂ := by
    have run := scaleLength_executes (extra+29) (w 4) (w 23) (w 31)
      (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (a-3) s₁
      (by simp [s₁,w.injective.eq_iff,workEmpty])
    simpa [s₁,s₂,v₂,w.injective.eq_iff,capacityLength,← List.append_assoc,← List.replicate_add,Nat.add_comm] using run
  have third : Executes (addScaledDifference (extra+26) w.ordinaryCountRoles (a-1)) s₂
      (addScaledDifferenceCost width capacity (a-1)) s₃ := by
    have run := addScaledDifference_executes (extra+26) w.ordinaryCountRoles (a-1) s₂
      (by simp [GeneratorWorkspace.ordinaryCountRoles,generatorOrdinarySelection,s₂,w.injective.eq_iff,differenceEmpty])
      (by simp [GeneratorWorkspace.ordinaryCountRoles,generatorOrdinarySelection,s₂,w.injective.eq_iff,counterEmpty])
      (by simp [GeneratorWorkspace.ordinaryCountRoles,generatorOrdinarySelection,s₂,w.injective.eq_iff,workEmpty])
    simpa [GeneratorWorkspace.ordinaryCountRoles,generatorOrdinarySelection,s₂,s₃,v₃,w.injective.eq_iff,
      widthLength,capacityLength,← List.append_assoc,← List.replicate_add,Nat.add_comm] using run
  have fourth : Executes (addScaledDifference (extra+26) w.binaryCountRoles b) s₃
      (addScaledDifferenceCost capacity 1 b) s₄ := by
    have run := addScaledDifference_executes (extra+26) w.binaryCountRoles b s₃
      (by simp [GeneratorWorkspace.binaryCountRoles,generatorBinaryCountSelection,s₃,w.injective.eq_iff,differenceEmpty])
      (by simp [GeneratorWorkspace.binaryCountRoles,generatorBinaryCountSelection,s₃,w.injective.eq_iff,counterEmpty])
      (by simp [GeneratorWorkspace.binaryCountRoles,generatorBinaryCountSelection,s₃,w.injective.eq_iff,workEmpty])
    simpa [GeneratorWorkspace.binaryCountRoles,generatorBinaryCountSelection,s₃,s₄,v₄,w.injective.eq_iff,
      capacityLength,unitLength,← List.append_assoc,← List.replicate_add,Nat.add_comm] using run
  have fifth : Executes (addScaledDifference (extra+26) w.transitionCountRoles d) s₄
      (addScaledDifferenceCost cells width d) s₅ := by
    have run := addScaledDifference_executes (extra+26) w.transitionCountRoles d s₄
      (by simp [GeneratorWorkspace.transitionCountRoles,generatorTransitionCountSelection,s₄,w.injective.eq_iff,differenceEmpty])
      (by simp [GeneratorWorkspace.transitionCountRoles,generatorTransitionCountSelection,s₄,w.injective.eq_iff,counterEmpty])
      (by simp [GeneratorWorkspace.transitionCountRoles,generatorTransitionCountSelection,s₄,w.injective.eq_iff,workEmpty])
    simpa [GeneratorWorkspace.transitionCountRoles,generatorTransitionCountSelection,s₄,s₅,v₅,w.injective.eq_iff,
      cellsLength,widthLength,← List.append_assoc,← List.replicate_add,Nat.add_comm] using run
  have combined := first.sequence (second.sequence (third.sequence (fourth.sequence fifth)))
  have value : v₅=generatorCountCoreValue program cells width capacity := by
    dsimp only [v₅,v₄,v₃,v₂,v₁,a,h,b,d,generatorCountCoreValue]
    simp only [Nat.mul_comm]
  simpa only [generatorCountCore,generatorCountCoreCost,s₅,value] using combined

end Counting.External.CookLevin.StackGenerator
