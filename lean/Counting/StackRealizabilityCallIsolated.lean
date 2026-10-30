import Counting.StackRealizabilityCallFile
import Counting.StackRegisterFrames

namespace Counting.StackMachine.RealizabilityCall
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

def runVerifier : Routine 128 := mapRegisters localRoles (isolate RealizabilityCheck.totalVerifier)

/-- The concrete total verifier is callable twice without corrupting the
caller's saved encodings. The cost includes erasing every private cell. -/
theorem runVerifier_executes (data : Fin 30→List Bool) (input : List Bool) :
    ∃ time ≤ 101*(Complexity.polynomial RealizabilityCheck.verifierCoefficient 25 input.length+input.length+3),
      Executes runVerifier (Function.update (file data) 0 input) time
        (Function.update (file data) 1 [RealizabilityCheck.encodedVerifier input]) := by
  obtain ⟨time,bound,run⟩ := isolate_executes RealizabilityCheck.totalVerifier _ _
    RealizabilityCheck.verifier_computes input
  refine ⟨time,bound,?_⟩
  apply relocate_executes_frame (isolate RealizabilityCheck.totalVerifier) localRoles
    (Function.update (file data) 0 input)
    (Function.update (file data) 1 [RealizabilityCheck.encodedVerifier input])
    (inputStore 98 input) (outputStore 98 [RealizabilityCheck.encodedVerifier input]) time _ _ _ run
  · funext i
    by_cases same:i=0
    · subst i;simp [localRoles,inputStore]
    · have different : localRoles i≠0 := by
        intro equal;apply same;exact Fin.ext (congrArg (fun r:Fin 130=>r.val) equal)
      simp [different,inputStore,same]
  · intro i
    by_cases same:i=1
    · subst i;simp [localRoles,outputStore]
    · have different : localRoles i≠1 := by
        intro equal;apply same;exact Fin.ext (congrArg (fun r:Fin 130=>r.val) equal)
      simp [different,outputStore,same]
  · intro i outside
    have a:i≠0 := by intro same;subst i;exact outside 0 rfl
    have b:i≠1 := by intro same;subst i;exact outside 1 rfl
    simp [a,b]

end Counting.StackMachine.RealizabilityCall
