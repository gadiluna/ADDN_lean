import Counting.ExternalCoverInputValidation
import Counting.StackCompilerComplete

namespace Counting.External.CoverInputValidation
open StackMachine StackMachine.Routine
set_option backward.isDefEq.respectTransparency false

def canonicalWorkspace : SATVerification.SATWorkspace 0:=Function.Embedding.refl _
def stackValidator : Program :=
  (sequence (pushBit 1 true) (routine 0 canonicalWorkspace)).program

theorem stackValidator_computes : ComputesIn stackValidator (fun input=>[validInput input])
    (Complexity.polynomial (coefficient+2) 5) := by
  intro input
  let store:=(initial stackValidator input).store
  have empty (i : Fin 32) (different : i≠0) : store i=[] := by
    change (if i=0 then input else [])=[]
    exact if_neg different
  have pushing:=pushBit_executes (registers:=30) 1 true store
  rw [empty 1 (by decide)] at pushing
  let ready:=Function.update store 1 [true]
  have readyEmpty (i : Fin 32) (n0 : i≠0) (n1 : i≠1) : ready (canonicalWorkspace i)=[] := by
    simpa [canonicalWorkspace,ready,n1] using empty i n0
  obtain ⟨time,bound,execution⟩:=routine_executes 0 canonicalWorkspace ready (by simp [canonicalWorkspace,ready]) readyEmpty
  have source : ready (canonicalWorkspace 0)=input := by
    simp [canonicalWorkspace,ready,store,initial]
  rw [source] at bound
  obtain ⟨finish,ran,halted,finalStore⟩:=pushing.sequence execution
  refine ⟨1+1+time,finish,?_,⟨ran,halted⟩,?_⟩
  · change 1+1+time ≤ (coefficient+2)*(input.length+1)^5
    have one : 1 ≤ (input.length+1)^5:=Nat.one_le_pow _ _ (by omega)
    nlinarith only [bound,one]
  · rw [finalStore]
    have flag:=result_flag 0 canonicalWorkspace ready
    change result 0 canonicalWorkspace ready 1=[validInput (ready (canonicalWorkspace 0))] at flag
    exact flag.trans (congrArg (fun word=>[validInput word]) source)

def machineValidator : Machine.Program:=Compiler.compile stackValidator

/-- Total polynomial recognition of the precise X3C input convention,
including clean physical output on every malformed binary word. -/
theorem machineValidator_computesCleanIn : Complexity.ComputesCleanIn machineValidator
    (fun input=>[validInput input]) (Complexity.polynomial (20*(coefficient+37)^2) 12) := by
  have compiled:=Compiler.computesCleanIn_polynomial (coefficient+2) 5 stackValidator_computes
  exact compiled

end Counting.External.CoverInputValidation
