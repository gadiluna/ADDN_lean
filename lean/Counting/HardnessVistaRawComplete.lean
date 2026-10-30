import Counting.HardnessVistaRawMachine
import Counting.StackRealizabilityVistaMachine
import Counting.ComplexityInclusions

namespace Counting.HardnessVistaRaw
open Complexity

def AtMostOneVistaLanguage : Language := {word | Encoding.BinaryAtMostOneVista word}

theorem complementX3C_reduces_AtMostOneVista :
    ManyOnePoly External.CoverMachine.X3CLanguageᶜ AtMostOneVistaLanguage :=
  ⟨normalizedVista,normalizedVistaProgram,normalizedVistaCoefficient,normalizedVistaExponent,
    normalizedVista_computesCleanIn,fun word=>(normalizedVista_correct word).symm⟩

theorem AtMostOneVista_coNPHard : coNPHard AtMostOneVistaLanguage :=
  External.CoverMachine.X3C_NPHard.complement.of_reduction complementX3C_reduces_AtMostOneVista

/-- Complete membership and hardness in the actual finite-alphabet machine
model, with the malformed-vista empty-spectrum convention. -/
theorem AtMostOneVista_coNPComplete : coNPComplete AtMostOneVistaLanguage :=
  ⟨StackMachine.VistaComplement.BinaryAtMostOneVista_in_coNP,AtMostOneVista_coNPHard⟩

/-- The reductions witnessing hardness produce only valid vistas realizable
with exactly one leader, for every input of every source coNP language. -/
theorem AtMostOneVista_realizable_one_leader_hard (source : Language) (member : coNP source) :
    ∃ f program coefficient exponent,
      ComputesCleanIn program f (polynomial coefficient exponent) ∧
      (∀ word,word∈source ↔ Encoding.BinaryAtMostOneVista (f word)) ∧
      ∀ word,∃ view order,Encoding.vistaInput.decodeExact (f word)=some (view,1) ∧
        view.valid=true ∧ Realizability.Realizable 1 order view.denotes := by
  obtain ⟨f,program,c,k,computes,correct⟩ := External.CoverMachine.X3C_NPHard.complement source member
  refine ⟨normalizedVista ∘ f,Machine.compose program normalizedVistaProgram,
    compositionCoefficient c normalizedVistaCoefficient normalizedVistaExponent,
    compositionExponent k normalizedVistaExponent,computes.compose normalizedVista_computesCleanIn,?_,?_⟩
  · intro word
    exact (correct word).trans (normalizedVista_correct (f word)).symm
  · intro word
    exact normalizedVista_restricted (f word)

theorem AtMostOneVista_not_P (separation : PNeNP) : ¬ P AtMostOneVistaLanguage :=
  AtMostOneVista_coNPHard.not_P separation

end Counting.HardnessVistaRaw
