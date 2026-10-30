import Counting.DagRawPhysical
import Counting.HardnessNetworkMachineReductionSpec
import Counting.HardnessEncodedRealization
import Counting.HardnessEncodedBounds

namespace Counting.HardnessVistaRaw
open Encoding

/-- Offline extraction keeps the valid import order of the first observer's
shared DAG. One leader is the fixed target restriction of this reduction. -/
def firstWord (input : Simulation.Input) : List Bool :=
  vistaInput.encode ((rawInputVistas input)[0]?.getD (Executable.initialVista false), 1)

def extractFirst (word : List Bool) : List Bool :=
  match networkInput.decodeExact word with
  | none => []
  | some input => firstWord input

theorem extractFirst_encoded (input : Simulation.Input) :
    extractFirst (networkInput.encode input) = firstWord input := by
  simp only [extractFirst, (networkInput.decodeExact_iff _ _).mpr rfl]

def leaderVista {q m : Nat} (inst : X3C.Instance q m) : Executable.Vista :=
  rawAgentVista (HardnessEncoded.input inst) (HardnessEncoded.observer inst)

theorem firstWord_baseline {q m : Nat} (inst : X3C.Instance q m) :
    firstWord (HardnessEncoded.input inst) = vistaInput.encode (leaderVista inst, 1) := by
  have inside : 0 < (rawInputVistas (HardnessEncoded.input inst)).size := by
    simp only [rawInputVistas_size, HardnessEncoded.input_agents]
    omega
  simp only [firstWord, leaderVista, rawAgentVista, HardnessEncoded.observer,
    Array.getElem?_eq_getElem inside, Option.getD_some]

theorem leaderVista_valid {q m : Nat} (inst : X3C.Instance q m) :
    (leaderVista inst).valid = true :=
  (rawInputVistas_correct (HardnessEncoded.input inst) (HardnessEncoded.observer inst)).1

theorem leaderVista_correct {q m : Nat} (inst : X3C.Instance q m) (large : 2 ≤ q) :
    Realizability.AtMostOneVista 1 (leaderVista inst).denotes ↔
      ¬ ∃ chosen, inst.IsExactCover chosen := by
  have bridge := rawAgentVista_atMostOne_iff (HardnessEncoded.input inst) (HardnessEncoded.observer inst)
  rw [HardnessEncoded.input_leaderCount] at bridge
  change Realizability.AtMostOneVista 1
    (rawAgentVista (HardnessEncoded.input inst) (HardnessEncoded.observer inst)).denotes ↔ _
  rw [bridge, HardnessEncoded.input_atMostOne_iff, HardnessEncoded.observer_equiv]
  exact HardnessReduction.atMostOneVista_iff_noExactCover inst large

theorem leaderVista_realizable {q m : Nat} (inst : X3C.Instance q m) (large : 2 ≤ q) :
    Realizability.Realizable 1 (X3C.baselineMass q m+1) (leaderVista inst).denotes := by
  have admissible := networkValid_admissible (HardnessEncoded.input inst)
    (HardnessEncoded.input_valid inst large)
  rw [HardnessEncoded.input_leaderCount] at admissible
  obtain ⟨_, depth, physical⟩ := rawInputVistas_correct
    (HardnessEncoded.input inst) (HardnessEncoded.observer inst)
  apply (HardnessEncoded.realizable_decode_iff (leaderVista inst) _ _ _ _ depth physical).mpr
  have actual := Realizability.actual_history_realizable 1
    (inputGraph (HardnessEncoded.input inst)) (inputLeader (HardnessEncoded.input inst))
    (HardnessEncoded.input inst).rounds.size admissible (HardnessEncoded.observer inst)
  simpa only [InputAgent, Fintype.card_fin, HardnessEncoded.input_agents, inputHistory] using actual

theorem firstWord_correct {q m : Nat} (inst : X3C.Instance q m) (large : 2 ≤ q) :
    BinaryAtMostOneVista (firstWord (HardnessEncoded.input inst)) ↔
      ¬ ∃ chosen, inst.IsExactCover chosen := by
  rw [firstWord_baseline]
  unfold BinaryAtMostOneVista binaryVistaSpectrum
  simp only [(vistaInput.decodeExact_iff _ _).mpr rfl]
  rw [Realizability.encodedSpectrum_valid 1 _ (leaderVista_valid inst)]
  exact leaderVista_correct inst large

def normalizedVista (word : List Bool) : List Bool :=
  extractFirst (HardnessNetworkMachine.normalizedNetwork word)

/-- The raw reduction has exactly the same language semantics as the
canonical vista reduction, with no equality of storage orders required. -/
theorem normalizedVista_correct (word : List Bool) :
    BinaryAtMostOneVista (normalizedVista word) ↔ ¬ X3CEncoding.BinaryX3C word := by
  obtain ⟨input, encoded, large, distinct⟩ :=
    External.CoverNormalization.normalizeWord_parameters word
  let data : X3C.Instance input.1 input.2.1 :=
    ⟨input.2.2.triples, input.2.2.triple_card, distinct⟩
  have same : HardnessNetworkMachine.normalizedNetwork word = HardnessEncoded.networkBits data := by
    unfold HardnessNetworkMachine.normalizedNetwork
    rw [←encoded, HardnessNetworkMachine.networkTransform_encoded]
    exact HardnessNetworkMachine.networkWord_coefficients data
  rw [normalizedVista, same]
  change BinaryAtMostOneVista (extractFirst (networkInput.encode (HardnessEncoded.input data))) ↔ _
  rw [extractFirst_encoded, firstWord_correct data large]
  have yes : (∃ chosen, data.IsExactCover chosen) ↔ X3CEncoding.BinaryX3C word := by
    change (∃ chosen, input.2.2.IsExactCover chosen) ↔ _
    rw [←X3CEncoding.encoded_yes_iff input, encoded,
      External.CoverNormalization.normalizeWord_yes_iff]
  exact not_congr yes

/-- All source bitwords, including malformed ones, produce a valid vista
realizable with exactly one leader. -/
theorem normalizedVista_restricted (word : List Bool) :
    ∃ view order, vistaInput.decodeExact (normalizedVista word) = some (view, 1) ∧
      view.valid = true ∧ Realizability.Realizable 1 order view.denotes := by
  obtain ⟨input, encoded, large, distinct⟩ :=
    External.CoverNormalization.normalizeWord_parameters word
  let data : X3C.Instance input.1 input.2.1 :=
    ⟨input.2.2.triples, input.2.2.triple_card, distinct⟩
  have same : HardnessNetworkMachine.normalizedNetwork word = HardnessEncoded.networkBits data := by
    unfold HardnessNetworkMachine.normalizedNetwork
    rw [←encoded, HardnessNetworkMachine.networkTransform_encoded]
    exact HardnessNetworkMachine.networkWord_coefficients data
  refine ⟨leaderVista data, X3C.baselineMass input.1 input.2.1+1, ?_,
    leaderVista_valid data, leaderVista_realizable data large⟩
  rw [normalizedVista, same]
  change vistaInput.decodeExact (extractFirst (networkInput.encode (HardnessEncoded.input data))) = _
  rw [extractFirst_encoded, firstWord_baseline]
  exact (vistaInput.decodeExact_iff _ _).mpr rfl

theorem firstWord_length (input : Simulation.Input) (nonempty : 0 < input.leaders.size) :
    (firstWord input).length ≤ 203*((networkInput.encode input).length+1)^5 := by
  let receiver : InputAgent input := ⟨0, nonempty⟩
  have bound := rawInputVistas_encoding_length input receiver
  have inside : 0 < (rawInputVistas input).size := by simpa using nonempty
  have positive : 1 ≤ ((networkInput.encode input).length+1)^5 := Nat.one_le_pow 5 _ (by omega)
  simp only [firstWord, Array.getElem?_eq_getElem inside, Option.getD_some, vistaInput_length,
    Nat.size_one, Nat.reduceMul, Nat.reduceAdd]
  dsimp only [receiver] at bound
  omega

end Counting.HardnessVistaRaw
