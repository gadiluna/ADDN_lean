import Counting.StackAuditCompleteDescendant

namespace Counting.StackMachine.AuditComplete
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def suffixBudget (vista : Executable.Vista) (candidate last anchor : Nat) (values : Option (Array Rat)) : Nat :=
  30*((AuditPostSolver.inputWord vista candidate anchor values).length+1)+
  AuditPostSolver.completeCoefficient*((AuditPostSolver.inputWord vista candidate anchor values).length+1)^51+
  weightsBudget vista anchor last (AuditPostSolver.result vista candidate anchor values)+2

abbrev suffixComplete : Routine 62 := sequence postSolverInput (sequence postSolverCall handleWeights)

/-- The concrete post-solver and descendant machines implement all remaining
audit checks and return the same optional complete witness as the program. -/
theorem suffixComplete_executes (vista : Executable.Vista) (leaders candidate last anchor : Nat)
    (values : Option (Array Rat)) (anchorBound:anchor≤ vista.nodes.size)
    (lastBound:last≤ vista.nodes.size) (valid:vista.valid=true) :
    ∃ time≤ suffixBudget vista candidate last anchor values,
      Executes suffixComplete
        (file [] (AuditPositive.inputWord values) (metadata vista leaders candidate last anchor.bits [])) time
        (file [] (witnessWord (Executable.auditSuffix? vista candidate last anchor values))
          (metadata vista leaders candidate last anchor.bits
            (optionalWeightsWord (AuditPostSolver.result vista candidate anchor values)))) := by
  obtain ⟨a,abound,arun⟩:=postSolverInput_executes vista leaders candidate last anchor values
  obtain ⟨b,bbound,brun⟩:=postSolverCall_executes vista candidate anchor values anchorBound valid
    (metadata vista leaders candidate last anchor.bits [])
  obtain ⟨c,cbound,crun⟩:=handleWeights_executes vista leaders candidate last anchor
    (AuditPostSolver.result vista candidate anchor values) lastBound
  rw [←suffix_eq] at crun
  exact ⟨_,by dsimp only [suffixBudget];omega,arun.sequence (brun.sequence crun)⟩

def solvedValues (vista : Executable.Vista) (leaders anchor : Nat) : Option (Array Rat) :=
  Executable.solveLinear? (Executable.levelNodes vista anchor).length
    (Executable.anchorRows vista anchor leaders)

def selectedBudget (vista : Executable.Vista) (leaders candidate last anchor : Nat) : Nat :=
  30*((AnchorMatrix.inputWord anchor leaders vista).length+1)+
  AnchorSolve.polynomialCoefficient*((AnchorMatrix.inputWord anchor leaders vista).length+1)^4500+
  suffixBudget vista candidate last anchor (solvedValues vista leaders anchor)+2

abbrev selected : Routine 62 := sequence solverInput (sequence solverCall suffixComplete)

/-- A successful prefix invokes exactly the concrete anchor solver, once,
and then runs every suffix check with its serialized answer. -/
theorem selected_executes (vista : Executable.Vista) (leaders candidate last anchor : Nat)
    (anchorBound:anchor≤ vista.nodes.size) (lastBound:last≤ vista.nodes.size) (valid:vista.valid=true) :
    ∃ time≤ selectedBudget vista leaders candidate last anchor,
      Executes selected
        (file [] [] (metadata vista leaders candidate last anchor.bits [])) time
        (file [] (witnessWord (Executable.auditSuffix? vista candidate last anchor (solvedValues vista leaders anchor)))
          (metadata vista leaders candidate last anchor.bits
            (optionalWeightsWord (AuditPostSolver.result vista candidate anchor (solvedValues vista leaders anchor))))) := by
  obtain ⟨a,abound,arun⟩:=solverInput_executes vista leaders candidate last anchor
  obtain ⟨b,bbound,brun⟩:=solverCall_executes vista anchor leaders
    (metadata vista leaders candidate last anchor.bits [])
  obtain ⟨c,cbound,crun⟩:=suffixComplete_executes vista leaders candidate last anchor
    (solvedValues vista leaders anchor) anchorBound lastBound valid
  have answer : AnchorSolve.resultWord vista anchor leaders=AuditPositive.inputWord (solvedValues vista leaders anchor) := rfl
  rw [answer] at brun
  exact ⟨_,by dsimp only [selectedBudget];omega,arun.sequence (brun.sequence crun)⟩

end Counting.StackMachine.AuditComplete
