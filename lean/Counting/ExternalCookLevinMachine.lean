import Counting.ExternalGeneratorCost
import Counting.StackCompilerComplete

namespace Counting.External.CookLevin.StackGenerator

theorem stackGenerator_computes (program : Machine.Program)
    (coefficient exponent witnessCoefficient witnessExponent : Nat) :
    StackMachine.ComputesIn (stackGenerator program coefficient exponent witnessCoefficient witnessExponent)
      (reduce program coefficient exponent witnessCoefficient witnessExponent)
      (Complexity.polynomial (generatorCoefficient program coefficient exponent witnessCoefficient witnessExponent)
        (generatorExponent exponent witnessExponent)) := by
  intro input
  obtain ⟨transitions,finish,bound,halted,output⟩ := stackGenerator_halts program
    coefficient exponent witnessCoefficient witnessExponent input
  exact ⟨transitions,finish,bound.trans (generatorCost_polynomial program input coefficient exponent
    witnessCoefficient witnessExponent),halted,output⟩

/-- An executable five-symbol Turing machine that writes the entire canonical
CNF reduction on a clean tape. Its finite control depends only on the verifier
and the four fixed polynomial parameters. -/
def machineGenerator (program : Machine.Program)
    (coefficient exponent witnessCoefficient witnessExponent : Nat) : Machine.Program :=
  StackMachine.Compiler.compile (stackGenerator program coefficient exponent witnessCoefficient witnessExponent)

theorem machineGenerator_computesCleanIn (program : Machine.Program)
    (coefficient exponent witnessCoefficient witnessExponent : Nat) :
    Complexity.ComputesCleanIn (machineGenerator program coefficient exponent witnessCoefficient witnessExponent)
      (reduce program coefficient exponent witnessCoefficient witnessExponent)
      (Complexity.polynomial
        (20*(generatorCoefficient program coefficient exponent witnessCoefficient witnessExponent+35)^2)
        (2*(generatorExponent exponent witnessExponent+1))) := by
  exact StackMachine.Compiler.computesCleanIn_polynomial _ _
    (stackGenerator_computes program coefficient exponent witnessCoefficient witnessExponent)

end Counting.External.CookLevin.StackGenerator

namespace Counting.External.CookLevin

/-- Cook--Levin hardness with an actual polynomial-time Turing transducer;
no runtime premise is imposed on the reduction generator. -/
theorem SAT_NPHard : Complexity.NPHard SAT := by
  intro language np
  obtain ⟨program,coefficient,exponent,witnessCoefficient,witnessExponent,_running,correct⟩ :=
    NP_exists_reduction language np
  refine ⟨reduce program coefficient exponent witnessCoefficient witnessExponent,
    StackGenerator.machineGenerator program coefficient exponent witnessCoefficient witnessExponent,
    _,_,StackGenerator.machineGenerator_computesCleanIn program coefficient exponent witnessCoefficient witnessExponent,?_⟩
  intro input
  exact (correct input).symm

end Counting.External.CookLevin
