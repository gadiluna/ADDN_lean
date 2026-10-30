import Counting.ComplexityModel

/-! Complement laws obtained by changing the accepting control labels of
the actual finite machine. Transitions, halting and running time are
preserved exactly. The reduction laws reuse the same clean transducer. -/
namespace Counting.Machine

def complement (program : Program) : Program :=
  { program with accept := fun control => !program.accept control }

def complementConfig {program : Program} (config : Config program) : Config (complement program) :=
  ⟨config.control, config.tape⟩

theorem complement_step (program : Program) (config : Config program) :
    step (complement program) (complementConfig config) = (step program config).map complementConfig := by
  simp only [step, complement, complementConfig, Option.map_map]
  rfl

theorem complement_run (program : Program) (steps : Nat) (config : Config program) :
    run (step (complement program)) steps (complementConfig config) =
      (run (step program) steps config).map complementConfig :=
  (run_simulation _ _ _ (fun config => (complement_step program config).symm) steps config).symm

theorem complement_halts {program : Program} {input : List Bool} {steps : Nat} {output : Config program}
    (halted : HaltsAt program input steps output) :
    HaltsAt (complement program) input steps (complementConfig output) := by
  constructor
  · change run (step (complement program)) steps (complementConfig (initial program input)) = _
    rw [complement_run, halted.1]
    rfl
  · rw [complement_step, halted.2]
    rfl

theorem complement_accepts {program : Program} {input : List Bool} {steps : Nat} {output : Config program}
    (halted : HaltsAt program input steps output) :
    Accepts (complement program) input ↔ ¬ Accepts program input := by
  rw [accepts_iff_of_halts (complement_halts halted), accepts_iff_of_halts halted]
  change (!program.accept output.control) = true ↔ ¬ program.accept output.control = true
  cases program.accept output.control <;> decide

end Counting.Machine

namespace Counting.Complexity
open Machine

theorem RunsIn.complement {program : Program} {bound : Nat → Nat} (total : RunsIn program bound) :
    RunsIn (Machine.complement program) bound := by
  intro input
  obtain ⟨steps, output, cost, halted⟩ := total input
  exact ⟨steps, complementConfig output, cost, complement_halts halted⟩

theorem DecidesIn.complement {program : Program} {language : Language} {bound : Nat → Nat}
    (decides : DecidesIn program language bound) :
    DecidesIn (Machine.complement program) languageᶜ bound := by
  refine ⟨decides.1.complement, ?_⟩
  intro input
  obtain ⟨_, _, _, halted⟩ := decides.1 input
  rw [complement_accepts halted, decides.2 input]
  rfl

theorem P.complement {language : Language} (member : P language) : P languageᶜ := by
  obtain ⟨program, coefficient, exponent, decides⟩ := member
  exact ⟨Machine.complement program, coefficient, exponent, decides.complement⟩

theorem P_complement_iff (language : Language) : P languageᶜ ↔ P language := by
  constructor
  · intro member
    simpa only [compl_compl] using member.complement
  · exact P.complement

theorem NP_complement_iff (language : Language) : NP languageᶜ ↔ coNP language := Iff.rfl

theorem coNP_complement_iff (language : Language) : coNP languageᶜ ↔ NP language := by
  simp only [coNP, compl_compl]

theorem ManyOnePoly.complement {source target : Language} (reduction : ManyOnePoly source target) :
    ManyOnePoly sourceᶜ targetᶜ := by
  obtain ⟨function, program, coefficient, exponent, computes, correct⟩ := reduction
  exact ⟨function, program, coefficient, exponent, computes, fun input => not_congr (correct input)⟩

theorem ManyOnePoly_complement_iff (source target : Language) :
    ManyOnePoly sourceᶜ targetᶜ ↔ ManyOnePoly source target := by
  constructor
  · intro reduction
    simpa only [compl_compl] using reduction.complement
  · exact ManyOnePoly.complement

theorem NPHard.complement {language : Language} (hard : NPHard language) : coNPHard languageᶜ := by
  intro source sourceMember
  have reduction := hard sourceᶜ sourceMember
  simpa only [compl_compl] using reduction.complement

theorem coNPHard.complement {language : Language} (hard : coNPHard language) : NPHard languageᶜ := by
  intro source sourceMember
  have reduction := hard sourceᶜ ((coNP_complement_iff source).mpr sourceMember)
  simpa only [compl_compl] using reduction.complement

theorem NPComplete.complement {language : Language} (complete : NPComplete language) :
    coNPComplete languageᶜ :=
  ⟨(coNP_complement_iff language).mpr complete.1, complete.2.complement⟩

theorem coNPComplete.complement {language : Language} (complete : coNPComplete language) :
    NPComplete languageᶜ := ⟨complete.1, complete.2.complement⟩

end Counting.Complexity
