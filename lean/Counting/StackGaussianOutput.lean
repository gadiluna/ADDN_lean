import Counting.StackGaussianInput
import Counting.StackGaussianRhsBounds
import Counting.StoredGaussianDirectSolve
import Counting.PositiveNaturalsSpec

namespace Counting.StackMachine.GaussianBank
open Routine DirectedCounting.VerifiedGaussianAnchorSolver RationalSystem
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

def rhsRoles : Fin 13 ↪ Fin 53 := ⟨![37,1,2,3,42,5,6,7,8,9,52,11,12],by decide⟩
abbrev readRhs : Routine 51 := sequence initializeOuter (relocate GaussianRhs.extract rhsRoles)
abbrev successOutput : Routine 51 := sequence readRhs (pushBit 1 true)
abbrev formatOutput : Routine 51 := branchRead 45 successOutput (pushBit 1 false)
abbrev complete : Routine 51 := sequence generateInput formatOutput

def solutionStore {q : Nat} (state : GaussianState q) (output : List Bool) : Fin 53 → List Bool :=
  Function.update (Function.update (outerStore state q []) 37 []) 1 output

def encodedSolution {q : Nat} (state : GaussianState q) : List Bool :=
  (Encoding.optional Encoding.rationalRow).encode (if state.ok then some (List.ofFn state.system.rhs) else none)

def outputStore {q : Nat} (state : GaussianState q) : Fin 53 → List Bool :=
  if state.ok then solutionStore state (encodedSolution state)
  else Function.update (outerStore state q []) 1 (encodedSolution state)

def rhsCost {q : Nat} (system : RationalSystem q) : Nat :=
  5*q+3+2000*((Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix system)).length+q+2)^2

theorem readRhs_executes {q : Nat} (state : GaussianState q) :
    ∃ time ≤ rhsCost state.system,
      Executes readRhs (outerStore state q []) time
        (solutionStore state (Encoding.rationalRow.encode (List.ofFn state.system.rhs))) := by
  have initialized := initializeOuter_executes state q
  obtain ⟨time,bounded,ran⟩ := GaussianRhs.extract_augmented state.system
  have extracted : Executes (relocate GaussianRhs.extract rhsRoles)
      (outerStore state q (List.replicate q true)) time
      (solutionStore state (Encoding.rationalRow.encode (List.ofFn state.system.rhs))) := by
    apply relocate_executes_frame GaussianRhs.extract rhsRoles _ _ _ _ time _ _ _ ran
    · funext r;fin_cases r <;>
        simp [rhsRoles,outerStore,stateStore,stateSaved,ready,bank,MatrixAxpy.file,RowAxpy.file,
          GaussianRhs.state,GaussianRhs.file]
    · intro r;fin_cases r <;>
        simp [solutionStore,rhsRoles,outerStore,stateStore,stateSaved,ready,bank,MatrixAxpy.file,RowAxpy.file,
          GaussianRhs.state,GaussianRhs.file]
    · intro r outside
      have matrix := outside 0
      have output := outside 1
      have counter := outside 10
      fin_cases r <;> simp_all [solutionStore,rhsRoles,outerStore]
  exact ⟨_,by dsimp only [rhsCost];omega,initialized.sequence extracted⟩

@[simp] theorem solutionStore_output {q : Nat} (state : GaussianState q) (output : List Bool) :
    solutionStore state output 1=output := by simp [solutionStore]

theorem successOutput_executes {q : Nat} (state : GaussianState q) :
    ∃ time ≤ rhsCost state.system+2,
      Executes successOutput (outerStore state q []) time
        (solutionStore state (true::Encoding.rationalRow.encode (List.ofFn state.system.rhs))) := by
  obtain ⟨time,bounded,ran⟩ := readRhs_executes state
  have pushed := pushBit_executes (1 : Fin 53) true
    (solutionStore state (Encoding.rationalRow.encode (List.ofFn state.system.rhs)))
  simp only [solutionStore_output] at pushed
  have result : Function.update (solutionStore state (Encoding.rationalRow.encode (List.ofFn state.system.rhs))) 1
      (true::Encoding.rationalRow.encode (List.ofFn state.system.rhs))=
      solutionStore state (true::Encoding.rationalRow.encode (List.ofFn state.system.rhs)) := by
    simp [solutionStore]
  rw [result] at pushed
  exact ⟨_,by omega,ran.sequence pushed⟩

theorem formatOutput_executes {q : Nat} (state : GaussianState q) :
    ∃ time ≤ rhsCost state.system+5,
      Executes formatOutput (outerStore state q []) time (outputStore state) := by
  cases active : state.ok with
  | false =>
    have pushed := pushBit_executes (1 : Fin 53) false (outerStore state q [])
    have result : false::outerStore state q [] 1=encodedSolution state := by
      simp [encodedSolution,active,Encoding.optional,outerStore,stateStore,ready,bank,MatrixAxpy.file,RowAxpy.file]
    rw [result] at pushed
    have branch := branchRead_executes (45 : Fin 53) successOutput (pushBit 1 false) false []
      (outerStore state q []) (Function.update (outerStore state q []) 1 (encodedSolution state)) 1
      (by simp [outerStore,stateStore,stateSaved,ready,bank,active]) pushed
    refine ⟨4,by omega,?_⟩
    simpa only [outputStore,active,Bool.false_eq_true,if_false] using branch
  | true =>
    obtain ⟨time,bounded,ran⟩ := successOutput_executes state
    have result : true::Encoding.rationalRow.encode (List.ofFn state.system.rhs)=encodedSolution state := by
      simp [encodedSolution,active,Encoding.optional]
    rw [result] at ran
    have branch := branchRead_executes (45 : Fin 53) successOutput (pushBit 1 false) true []
      (outerStore state q []) (solutionStore state (encodedSolution state)) time
      (by simp [outerStore,stateStore,stateSaved,ready,bank,active]) ran
    refine ⟨time+3,by omega,?_⟩
    simpa only [outputStore,active,if_true] using branch

@[simp] theorem outputStore_output {q : Nat} (state : GaussianState q) :
    outputStore state 1=encodedSolution state := by
  unfold outputStore
  split <;> simp [solutionStore]

theorem encodedSolution_solve {q : Nat} (system : RationalSystem q) :
    encodedSolution (StoredGaussian.runGaussian system)=
      (Encoding.optional Encoding.rationalRow).encode ((StoredGaussian.solve? system).map List.ofFn) := by
  rw [StoredGaussian.solve_eq_direct]
  unfold encodedSolution
  split <;> rfl

end Counting.StackMachine.GaussianBank
