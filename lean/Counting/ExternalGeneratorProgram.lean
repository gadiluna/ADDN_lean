import Counting.ExternalGeneratorComplete

namespace Counting.External.CookLevin.StackGenerator
open StackMachine

/-- Physical stack input is register zero, output is register one. The
remaining named generator roles are assigned by an executable permutation. -/
def canonicalWorkspace : GeneratorWorkspace 0 :=
  ⟨![2,3,4,5,6,1,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,0,29,30,31],by decide⟩

def stackGenerator (program : Machine.Program)
    (coefficient exponent witnessCoefficient witnessExponent : Nat) : StackMachine.Program :=
  (generatorRoutine 0 canonicalWorkspace program coefficient exponent witnessCoefficient witnessExponent).program

/-- The concrete generated stack program computes the original CNF codec
on every input word, with the complete instruction-count expression. -/
theorem stackGenerator_halts (program : Machine.Program)
    (coefficient exponent witnessCoefficient witnessExponent : Nat) (input : List Bool) :
    ∃ transitions finish,
      transitions ≤ generatorCost program input coefficient exponent witnessCoefficient witnessExponent ∧
      StackMachine.HaltsAt (stackGenerator program coefficient exponent witnessCoefficient witnessExponent) input transitions finish ∧
      finish.store 1=reduce program coefficient exponent witnessCoefficient witnessExponent input := by
  let generated := stackGenerator program coefficient exponent witnessCoefficient witnessExponent
  let initialStore := (StackMachine.initial generated input).store
  have empty : ∀ i : Fin 32, i ≠ 28 → initialStore (canonicalWorkspace i)=[] := by
    intro i ne
    have different : canonicalWorkspace i ≠ 0 := by
      intro same
      apply ne
      exact canonicalWorkspace.injective (same.trans (show 0=canonicalWorkspace 28 from rfl))
    change (if canonicalWorkspace i=(0 : Fin 32) then input else [])=[]
    exact if_neg different
  obtain ⟨transitions,bound,result,run,output⟩ := generatorRoutine_executes 0 canonicalWorkspace program
    coefficient exponent witnessCoefficient witnessExponent initialStore empty
  obtain ⟨finish,executed,halted,finalStore⟩ := run
  have source : initialStore (canonicalWorkspace 28)=input := by
    change (if canonicalWorkspace 28=(0 : Fin 32) then input else [])=input
    exact if_pos rfl
  rw [source] at bound output
  refine ⟨transitions,finish,bound,⟨executed,halted⟩,?_⟩
  rw [finalStore]
  exact output

end Counting.External.CookLevin.StackGenerator
