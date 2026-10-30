import Counting.MachineFrameBoot
import Counting.MachineGate
import Counting.ComplexityComposition
import Counting.ComplexityComplements

/-! A concrete verifier witnessing P ⊆ NP. It requires an empty witness,
validates the self-delimiting input frame, and runs the original decider
on alternate tape cells. Neither decoding nor tape cleanup is assumed to
be a free operation. -/
namespace Counting.Machine

def framedVerifier (program : Program) : Program := gate frameBoot (strideProgram program)

theorem framedVerifier_halts {program : Program} {input : List Bool} {steps : Nat}
    {output : Config program} (halted : HaltsAt program input steps output) :
    ∃ finish, HaltsAt (framedVerifier program) (Encoding.frame input)
        (4 * input.length + 7 + 2 * steps) finish ∧
      (framedVerifier program).accept finish.control = program.accept output.control := by
  unfold framedVerifier
  let start : Config program := ⟨0, (bootOutput input).unstride⟩
  have same : (initial program input).denotes = start.denotes := by
    simp only [initial, Config.denotes, Tape.denotes_ofWord, start, bootOutput_decodes]
  obtain ⟨middle, middleRun, middleSame⟩ := run_transport program steps (initial program input) start output same halted.1
  have middleHalt : step program middle = none := halt_transport middleSame.symm halted.2
  obtain ⟨finishTape, simulation, decoded⟩ := stride_run program steps start middle (bootOutput input) rfl middleRun
  have finishHalt := stride_terminal program middle finishTape decoded middleHalt
  have zeroControl : strideControl program 0 0 = (0 : Control (strideProgram program)) := by
    apply Fin.ext
    simp only [strideControl, Fin.val_zero, Nat.zero_mul, Nat.zero_add]
  have initialRun : run (step (strideProgram program)) (2 * steps) ⟨0, bootOutput input⟩ =
      some (strideConfig program middle.control finishTape) := by
    simpa only [start, strideConfig, zeroControl] using simulation
  obtain ⟨finished, accept⟩ := gate_continue (second := strideProgram program)
    (frameBoot_frame input) rfl initialRun finishHalt
  refine ⟨gateSecond frameBoot (strideProgram program) (strideConfig program middle.control finishTape), ?_, ?_⟩
  · rw [show 4 * input.length + 7 + 2 * steps = 4 * input.length + 6 + 1 + 2 * steps by omega]
    exact finished
  · rw [accept, stride_accept]
    exact congrArg program.accept (congrArg Turing.TM0.Cfg.q middleSame)

theorem framedVerifier_accepts {program : Program} {input : List Bool} {steps : Nat}
    {output : Config program} (halted : HaltsAt program input steps output) :
    Accepts (framedVerifier program) (Encoding.frame input) ↔ Accepts program input := by
  obtain ⟨finish, finished, accepted⟩ := framedVerifier_halts halted
  rw [accepts_iff_of_halts finished, accepted, accepts_iff_of_halts halted]

end Counting.Machine

namespace Counting.Complexity
open Machine

theorem framedVerifier_cost (c k n m steps : Nat) (payload : m ≤ n)
    (bounded : steps ≤ polynomial c k m) :
    4 * m + 7 + 2 * steps ≤ polynomial (2*c + 11) (k+1) n := by
  have positive : 0 < n+1 := by omega
  have grows : n+1 ≤ (n+1)^(k+1) := Nat.le_pow (by omega)
  have power := (Nat.pow_le_pow_left (Nat.add_le_add_right payload 1) k).trans
    (Nat.pow_le_pow_right positive (Nat.le_succ k))
  have cost := Nat.mul_le_mul_left c power
  simp only [Nat.succ_eq_add_one] at cost
  unfold polynomial at *
  nlinarith

theorem RunsIn.framedVerifier {program : Program} {c k : Nat}
    (runs : RunsIn program (polynomial c k)) :
    RunsIn (framedVerifier program) (polynomial (2*c + 11) (k+1)) := by
  intro input
  obtain ⟨bootSteps, bootResult, bootCost, bootHalts, bootAccepted⟩ := frameBoot_total input
  by_cases accepted : frameBoot.accept bootResult.control = true
  · obtain ⟨payload, same, result⟩ := bootAccepted accepted
    subst input
    obtain ⟨steps, output, cost, halted⟩ := runs payload
    obtain ⟨finish, finished, _⟩ := framedVerifier_halts halted
    refine ⟨_, finish, framedVerifier_cost c k _ _ steps ?_ cost, finished⟩
    rw [Encoding.frame_length]
    omega
  · obtain ⟨finished, _⟩ := gate_reject (second := strideProgram program) bootHalts (Bool.eq_false_iff.mpr accepted)
    refine ⟨bootSteps, _, ?_, finished⟩
    have power : input.length+1 ≤ (input.length+1)^(k+1) := Nat.le_pow (by omega)
    unfold polynomial
    nlinarith

/-- Inclusion of the deterministic class in the certificate class, with
an explicit finite-state verifier and a verified polynomial transition
bound on all binary inputs. The sole permitted witness is the empty word. -/
theorem P.subset_NP {language : Language} (member : P language) : NP language := by
  obtain ⟨program, c, k, runs, correct⟩ := member
  refine ⟨framedVerifier program, 2*c+11, k+1, 0, 0, runs.framedVerifier, ?_⟩
  intro input
  obtain ⟨steps, output, _, halted⟩ := runs input
  have accepts := framedVerifier_accepts halted
  constructor
  · intro positive
    refine ⟨[], Nat.zero_le _, ?_⟩
    simpa only [Encoding.pairWords, List.append_nil] using accepts.mpr ((correct input).mpr positive)
  · rintro ⟨witness, size, accepted⟩
    have empty : witness = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero (by
      simpa only [polynomial, Nat.zero_mul] using size))
    subst witness
    apply (correct input).mp
    apply accepts.mp
    simpa only [Encoding.pairWords, List.append_nil] using accepted

theorem NPHard.not_P {language : Language} (hard : NPHard language) (separation : PNeNP) : ¬ P language := by
  intro easy
  apply separation
  intro source
  exact ⟨P.subset_NP, fun member => P.of_reduction (hard source member) easy⟩

theorem coNPHard.not_P {language : Language} (hard : coNPHard language) (separation : PNeNP) : ¬ P language := by
  intro easy
  exact (hard.complement.not_P separation) easy.complement

end Counting.Complexity
