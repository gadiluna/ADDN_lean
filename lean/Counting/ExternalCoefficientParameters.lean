import Counting.ExternalCoefficientBaseline
import Counting.ExternalCoefficientHigh

namespace Counting.External.CoefficientMachine
open StackMachine StackMachine.Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def parameterScratch : List (Fin 64) := baseScratch++highScratch++baselineScratch
def prepareParameters (extra : Nat) (w : Workspace extra) : Routine (extra+62) :=
  sequence (prepareBase extra w) (sequence (prepareHigh extra w) (prepareBaseline extra w))
def parameterCost (q : Nat) := 100*(q+1)^2+1+
  (highCost (X3C.base q).bits.length (3*q)+1+
    baselineCost q (3*q) (X3C.base q).bits.length (X3C.high q).bits.length ((3*q+1)*(X3C.base q).size))
def parameterResult (w : Workspace extra) (store : Fin (extra+64) → List Bool) (q : Nat) :=
  Function.update (Function.update (Function.update (Function.update store (w 27) (List.replicate q true))
    (w 52) (X3C.base q).bits) (w 54) (X3C.high q).bits) (w 55) (X3C.target q).bits

theorem prepareParameters_executes (extra : Nat) (w : Workspace extra)
    (store : Fin (extra+64) → List Bool) (q : Nat)
    (universeCounter : store (w 17)=List.replicate (3*q) true)
    (empty : ∀ i∈parameterScratch,store (w i)=[]) :
    ∃ time ≤ parameterCost q,
      Executes (prepareParameters extra w) store time (parameterResult w store q) := by
  obtain ⟨baseTime,baseBound,baseRun⟩:=prepareBase_executes extra w store q universeCounter
    (fun i member=>empty i (by simp only [parameterScratch,List.mem_append];exact Or.inl (Or.inl member)))
  let based:=Function.update (Function.update store (w 27) (List.replicate q true)) (w 52) (X3C.base q).bits
  have basedEmpty (i : Fin 64) (member : i∈highScratch) : based (w i)=[] := by
    have n27 : i≠27 := by intro same;subst i;simp [highScratch] at member
    have n52 : i≠52 := by intro same;subst i;simp [highScratch] at member
    simpa [based,w.injective.eq_iff,n27,n52] using
      empty i (by simp only [parameterScratch,List.mem_append];exact Or.inl (Or.inr member))
  obtain ⟨highTime,highBound,highRun⟩:=prepareHigh_executes extra w based (3*q)
    (by simp [based,w.injective.eq_iff,universeCounter]) basedEmpty
  have baseAt : based (w 52)=(X3C.base q).bits := by simp [based]
  rw [baseAt] at highBound highRun
  rw [Encoding.value_bits] at highRun
  let highStore:=Function.update based (w 54) (X3C.high q).bits
  have highEmpty (i : Fin 64) (member : i∈baselineScratch) : highStore (w i)=[] := by
    have n27 : i≠27 := by intro same;subst i;simp [baselineScratch,productScratch,geometricScratch] at member
    have n52 : i≠52 := by intro same;subst i;simp [baselineScratch,productScratch,geometricScratch] at member
    have n54 : i≠54 := by intro same;subst i;simp [baselineScratch,productScratch,geometricScratch] at member
    simpa [highStore,based,w.injective.eq_iff,n27,n52,n54] using
      empty i (by simp only [parameterScratch,List.mem_append];exact Or.inr member)
  obtain ⟨baselineTime,baselineBound,baselineRun⟩:=prepareBaseline_target_executes extra w highStore q
    (by simp [highStore,based,w.injective.eq_iff])
    (by simp [highStore,based,w.injective.eq_iff,universeCounter])
    (by simp [highStore,based,w.injective.eq_iff]) (by simp [highStore]) highEmpty
  refine ⟨baseTime+1+(highTime+1+baselineTime),?_,baseRun.sequence (highRun.sequence baselineRun)⟩
  unfold parameterCost
  omega

end Counting.External.CoefficientMachine
