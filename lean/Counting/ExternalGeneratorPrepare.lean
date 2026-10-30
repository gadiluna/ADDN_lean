import Counting.ExternalGeneratorDimensions
import Counting.ExternalGeneratorHeader
import Counting.ExternalCookLevinCounterCost

namespace Counting.External.CookLevin.StackGenerator
open StackMachine StackMachine.Routine

def generatorBoundsSelection : Fin 8 ↪ Fin 32 := ⟨![28,25,4,29,0,6,7,31],by decide⟩
def GeneratorWorkspace.boundsRoles (w : GeneratorWorkspace extra) : Workspace (extra+24) := generatorBoundsSelection.trans w

def generatorBounded (w : GeneratorWorkspace extra) (store : Fin (extra+32) → List Bool)
    (coefficient exponent witnessCoefficient witnessExponent : Nat) :=
  let input := store (w 28)
  let witness := Complexity.polynomial witnessCoefficient witnessExponent input.length
  let time := timeBound coefficient exponent input witness
  Function.update (Function.update (Function.update (Function.update store
    (w 25) (List.replicate (input.length+1) true)) (w 4) (List.replicate witness true))
    (w 29) (List.replicate (2*(input.length+1)+witness) true)) (w 0) (List.replicate time true)

def generatorPrepared (w : GeneratorWorkspace extra) (store : Fin (extra+32) → List Bool)
    (coefficient exponent witnessCoefficient witnessExponent : Nat) :=
  let input := store (w 28)
  let witness := Complexity.polynomial witnessCoefficient witnessExponent input.length
  let time := timeBound coefficient exponent input witness
  let width := MachineBridge.width (capacity input witness) time
  Function.update (Function.update (Function.update (Function.update
    (generatorBounded w store coefficient exponent witnessCoefficient witnessExponent)
      (w 2) (List.replicate (time+1) true)) (w 1) (List.replicate width true))
      (w 3) (Encoding.frame input)) (w 26) (List.replicate ((time+1)*width) true)

def generatorPrepare (extra : Nat) (w : GeneratorWorkspace extra)
    (coefficient exponent witnessCoefficient witnessExponent : Nat) : Routine (extra+30) :=
  sequence (boundsRoutine (extra+24) w.boundsRoles coefficient exponent witnessCoefficient witnessExponent)
    (sequence (offsetRoutine extra w) (sequence (widthRoutine extra w)
      (sequence (inputHeaderRoutine extra w) (cellsRoutine extra w))))

def generatorPrepareCost (input : List Bool) (coefficient exponent witnessCoefficient witnessExponent : Nat) :=
  let witness := Complexity.polynomial witnessCoefficient witnessExponent input.length
  let time := timeBound coefficient exponent input witness
  let width := MachineBridge.width (capacity input witness) time
  boundsCost input.length coefficient exponent witnessCoefficient witnessExponent+1+
    (5*time+4+1+(10*(time+1)+5*(2*(input.length+1)+witness)+9+1+
      (10*input.length+7+1+((5*width+9)*(time+1)+7))))

theorem generatorPrepare_executes (extra : Nat) (w : GeneratorWorkspace extra)
    (coefficient exponent witnessCoefficient witnessExponent : Nat) (store : Fin (extra+32) → List Bool)
    (empty : ∀ i : Fin 32, i ≠ 28 → store (w i)=[]) :
    Executes (generatorPrepare extra w coefficient exponent witnessCoefficient witnessExponent) store
      (generatorPrepareCost (store (w 28)) coefficient exponent witnessCoefficient witnessExponent)
      (generatorPrepared w store coefficient exponent witnessCoefficient witnessExponent) := by
  let input := store (w 28)
  let witness := Complexity.polynomial witnessCoefficient witnessExponent input.length
  let time := timeBound coefficient exponent input witness
  let width := MachineBridge.width (capacity input witness) time
  let bounded := generatorBounded w store coefficient exponent witnessCoefficient witnessExponent
  let offsetStore := Function.update bounded (w 2) (List.replicate (time+1) true)
  let widthStore := Function.update offsetStore (w 1) (List.replicate width true)
  let headerStore := Function.update widthStore (w 3) (Encoding.frame input)
  have first : Executes (boundsRoutine (extra+24) w.boundsRoles coefficient exponent witnessCoefficient witnessExponent)
      store (boundsCost input.length coefficient exponent witnessCoefficient witnessExponent) bounded := by
    have run := boundsRoutine_executes (extra+24) w.boundsRoles coefficient exponent witnessCoefficient witnessExponent store (by
      intro i ne
      fin_cases i
      · exact False.elim (ne rfl)
      all_goals
        simp [GeneratorWorkspace.boundsRoles,generatorBoundsSelection]
        apply empty
        decide)
    simpa [GeneratorWorkspace.boundsRoles,generatorBoundsSelection,bounded,generatorBounded,input] using run
  have second : Executes (offsetRoutine extra w) bounded (5*time+4) offsetStore := by
    apply offsetRoutine_executes extra w time bounded
    · simp [bounded,generatorBounded,time,witness,input]
    · simp [bounded,generatorBounded,w.injective.eq_iff,empty 2 (by decide)]
    · simp [bounded,generatorBounded,w.injective.eq_iff,empty 31 (by decide)]
  have widthEq : 2*(input.length+1)+witness+2*(time+1)=width := by
    dsimp only [width,MachineBridge.width,capacity]
    rw [Encoding.frame_length]
    omega
  have third : Executes (widthRoutine extra w) offsetStore
      (10*(time+1)+5*(2*(input.length+1)+witness)+9) widthStore := by
    have run := widthRoutine_executes extra w (time+1) (2*(input.length+1)+witness) offsetStore
      (by simp [offsetStore])
      (by simp [offsetStore,bounded,generatorBounded,w.injective.eq_iff,witness,input])
      (by simp [offsetStore,bounded,generatorBounded,w.injective.eq_iff,empty 1 (by decide)])
      (by simp [offsetStore,bounded,generatorBounded,w.injective.eq_iff,empty 31 (by decide)])
    simpa only [widthEq,widthStore] using run
  have fourth : Executes (inputHeaderRoutine extra w) widthStore (10*input.length+7) headerStore := by
    have run := inputHeaderRoutine_executes extra w widthStore
      (by simp [widthStore,offsetStore,bounded,generatorBounded,w.injective.eq_iff,empty 3 (by decide)])
      (by simp [widthStore,offsetStore,bounded,generatorBounded,w.injective.eq_iff,empty 30 (by decide)])
      (by simp [widthStore,offsetStore,bounded,generatorBounded,w.injective.eq_iff,empty 21 (by decide)])
      (by simp [widthStore,offsetStore,bounded,generatorBounded,w.injective.eq_iff,empty 31 (by decide)])
    simpa [headerStore,widthStore,offsetStore,bounded,generatorBounded,w.injective.eq_iff,input] using run
  have fifth : Executes (cellsRoutine extra w) headerStore ((5*width+9)*(time+1)+7)
      (generatorPrepared w store coefficient exponent witnessCoefficient witnessExponent) := by
    have run := cellsRoutine_executes extra w (time+1) width headerStore
      (by simp [headerStore,widthStore,offsetStore,w.injective.eq_iff])
      (by simp [headerStore,widthStore,w.injective.eq_iff])
      (by simp [headerStore,widthStore,offsetStore,bounded,generatorBounded,w.injective.eq_iff,empty 6 (by decide)])
      (by simp [headerStore,widthStore,offsetStore,bounded,generatorBounded,w.injective.eq_iff,empty 26 (by decide)])
      (by simp [headerStore,widthStore,offsetStore,bounded,generatorBounded,w.injective.eq_iff,empty 27 (by decide)])
      (by simp [headerStore,widthStore,offsetStore,bounded,generatorBounded,w.injective.eq_iff,empty 31 (by decide)])
    exact run
  exact first.sequence (second.sequence (third.sequence (fourth.sequence fifth)))

end Counting.External.CookLevin.StackGenerator
