import Counting.StackRealizabilityDepthFrame
import Counting.StackRealizabilityRoundAll
import Counting.StackEncodingBoundedNatural

namespace Counting.StackMachine.RealizabilityCheck
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option maxRecDepth 8000

def depthCountRoles : CountWorkspace 89 := ⟨![72,97,0,2,3,4,85,5,6,7,73],by decide⟩
def depthUnary : Routine 98 := sequence (ofProgram (ListPrograms.copyProgram 97 87 73 0))
  (sequence (boundedCount 89 depthCountRoles)
    (sequence (ofProgram (combineFlagsProgram 98 85)) (sequence (clear 72) (clear 87))))

def roundsReadyStore (vista : Executable.Vista) (values : List Nat) (ell order : Nat)
    (status : List Bool) : Store 98 :=
  roundFile (roundInputData vista.nodes.toList values order 0 status
    (roundOuterData (List.replicate (vista.node vista.bottom).level true)
      ![ell.bits,Encoding.vista.encode vista]))

/-- A bounded binary-to-unary machine prepares exactly the round counter.
The consumed budget is the explicit node table count; DAG validity proves
the depth fits that budget. The result is the exact full store of roundScan. -/
theorem depthUnary_executes (vista : Executable.Vista) (values : List Nat) (ell order : Nat)
    (valid : vista.valid=true) (accepted : Bool) (tail : List Bool) :
    ∃ time ≤ 100*(vista.nodes.size+(Encoding.natural.encode (vista.node vista.bottom).level).length+1)^3,
      Executes depthUnary (depthFramedStore vista values ell order (accepted::tail)) time
        (roundsReadyStore vista values ell order (accepted::tail)) := by
  let depth := (vista.node vista.bottom).level
  let start := depthFramedStore vista values ell order (accepted::tail)
  have copying := copy_executes 97 (87:Fin 100) 73 0 (by decide) (by decide) (by decide)
    start (by simp [start,depthFramedStore,inputCountStore,inputNodesStore,inputFieldsStore])
  have budgetAt : start 87=List.replicate vista.nodes.size true := by simp [start,depthFramedStore,inputCountStore]
  have emptyAt : start 73=[] := by simp [start,depthFramedStore,inputCountStore,inputNodesStore,inputFieldsStore]
  rw [budgetAt,emptyAt,List.append_nil,List.length_replicate] at copying
  let copied := Function.update start 73 (List.replicate vista.nodes.size true)
  have header : copied (depthCountRoles 0)=Encoding.natural.encode depth := by simp [copied,start,depthFramedStore,depthCountRoles,depth]
  obtain ⟨time,bound,counting⟩ := boundedNatural_executes 89 depthCountRoles copied depth header
    (by simp [copied,start,depthCountRoles,depthFramedStore,inputCountStore,inputNodesStore,inputFieldsStore])
    (by intro i member;fin_cases i <;> simp_all [copied,start,depthCountRoles,depthFramedStore,inputCountStore,inputNodesStore,inputFieldsStore])
  have fits : depth ≤ vista.nodes.size := Nat.le_of_lt (RealizabilityVerifier.valid_depth_lt_size vista valid)
  let counted := Function.update (Function.update start 97 (List.replicate depth true)) 85 (true::accepted::tail)
  have countedEq : boundedNaturalResult 89 depthCountRoles copied depth=counted := by
    simp only [boundedNaturalResult]
    funext i
    by_cases a:i=97 <;> by_cases b:i=73 <;> by_cases c:i=85 <;>
      simp_all [depthCountRoles,copied,start,depthFramedStore,inputCountStore,inputNodesStore,inputFieldsStore,
        counted]
  rw [countedEq] at counting
  have joining := combineFlags_executes 98 (85:Fin 100) counted accepted true tail (by simp [counted])
  let joined := Function.update start 97 (List.replicate depth true)
  have joinedEq : Function.update counted 85 ((accepted && true)::tail)=joined := by
    simp only [counted,Bool.and_true,Function.update_idem]
    have status : joined 85=accepted::tail := by
      simp [joined,start,depthFramedStore,inputCountStore,inputNodesStore,inputFieldsStore]
    rw [←status]
    exact Function.update_eq_self _ _
  rw [joinedEq] at joining
  have c0 := clear_executes (72:Fin 100) joined
  have codeAt : joined 72=Encoding.natural.encode depth := by simp [joined,start,depthFramedStore,depth]
  rw [codeAt] at c0
  let cleared := Function.update joined 72 []
  have c1 := clear_executes (87:Fin 100) cleared
  have countAt : cleared 87=List.replicate vista.nodes.size true := by
    simp [cleared,joined,start,depthFramedStore,inputCountStore]
  rw [countAt,List.length_replicate] at c1
  have final : Function.update cleared 87 []=roundsReadyStore vista values ell order (accepted::tail) := by
    funext i
    fin_cases i <;> simp [cleared,joined,start,depthFramedStore,inputCountStore,inputNodesStore,inputFieldsStore,
      roundsReadyStore,roundFile,roundInputData,roundOuterData,depth]
  rw [final] at c1
  change time ≤ 64*((copied (depthCountRoles 10)).length+(Encoding.natural.encode depth).length+1)^3 at bound
  have copiedBudget : (copied (depthCountRoles 10)).length = vista.nodes.size := by
    change (List.replicate vista.nodes.size true).length = vista.nodes.size
    exact List.length_replicate
  rw [copiedBudget] at bound
  let S := vista.nodes.size+(Encoding.natural.encode depth).length+1
  change time ≤ 64*S^3 at bound
  have linear : S ≤ S^3 := Nat.le_self_pow (by decide) _
  have one : 1 ≤ S^3 := Nat.one_le_pow _ _ (by dsimp only [S];omega)
  have small : vista.nodes.size+(Encoding.natural.encode depth).length ≤ S := by dsimp only [S];omega
  exact ⟨_,by change 5*vista.nodes.size+2+1+(time+1+(3+1+((Encoding.natural.encode depth).length+1+1+(vista.nodes.size+1)))) ≤ 100*S^3;omega,
    copying.sequence (counting.sequence (joining.sequence (c0.sequence c1)))⟩

end Counting.StackMachine.RealizabilityCheck
