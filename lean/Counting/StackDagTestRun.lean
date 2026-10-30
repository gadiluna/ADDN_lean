import Counting.StackEncodingPairTests

/-! Test-only acceleration of the semantic interpreter. Every transition
is still exactly StackMachine.step; tabulating its finite store is proved
extensionally equal to the original configuration. This avoids long chains
of Function.update closures in large full-store regression examples. -/
namespace Counting.StackMachine.DagValidation.TestRun

def tabulate (program : Program) (config : Config program) : Config program:=
  let table:=Array.ofFn config.store
  ⟨config.control,fun r=>table[r]'(by simp [table])⟩

theorem tabulate_eq (program : Program) (config : Config program) : tabulate program config=config:=by
  cases config
  simp [tabulate]

def run (program : Program) : Nat → Nat → Config program → Option (Nat×Config program)
  | 0,_,_=>none
  | fuel+1,elapsed,config=>
    match step program config with
    | none=>some (elapsed,config)
    | some next=>run program fuel (elapsed+1) (tabulate program next)

theorem run_sound (program : Program) (fuel elapsed : Nat) (config : Config program)
    (steps : Nat) (finish : Config program) (result : run program fuel elapsed config=some (steps,finish)) :
    elapsed≤steps ∧ Machine.run (step program) (steps-elapsed) config=some finish ∧ step program finish=none:=by
  induction fuel generalizing elapsed config with
  | zero=>simp [run] at result
  | succ fuel ih=>
    simp only [run] at result
    cases nextEq:step program config with
    | none=>
      simp only [nextEq] at result
      cases result
      exact ⟨le_refl _,by simp,nextEq⟩
    | some next=>
      simp only [nextEq,tabulate_eq] at result
      obtain ⟨bound,ran,halted⟩:=ih (elapsed+1) next result
      refine ⟨by omega,?_,halted⟩
      have distance : steps-elapsed=steps-(elapsed+1)+1:=by omega
      rw [distance,Machine.run, nextEq,Option.bind_some]
      exact ran

end Counting.StackMachine.DagValidation.TestRun
