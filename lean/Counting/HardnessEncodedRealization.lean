import Counting.HardnessEncodedNetwork

namespace Counting.HardnessEncoded
open Encoding

theorem realizable_decode_iff (v : Executable.Vista) (ell N t : Nat) (H : FullHistory t)
    (depth : (v.node v.bottom).level = t) (physical : Executable.decodeNode v t v.bottom = H) :
    Realizability.Realizable ell N v.denotes ↔ Realizability.Realizable ell N H := by
  subst t
  rw [← physical]
  rfl

/-- The computed leader DAG always satisfies the realizability restriction
in the hardness statement, with exactly one leader and the baseline order. -/
theorem leaderVista_realizable {q m : Nat} (inst : X3C.Instance q m) (large : 2 ≤ q) :
    Realizability.Realizable 1 (X3C.baselineMass q m+1) (leaderVista inst).denotes := by
  have admissible := networkValid_admissible (input inst) (input_valid inst large)
  rw [input_leaderCount] at admissible
  obtain ⟨_, depth, physical⟩ := inputVistas_correct (input inst) (observer inst)
  apply (realizable_decode_iff (leaderVista inst) _ _ _ _ depth physical).mpr
  have actual := Realizability.actual_history_realizable 1 (inputGraph (input inst))
    (inputLeader (input inst)) (input inst).rounds.size admissible (observer inst)
  simpa only [InputAgent, Fintype.card_fin, input_agents, inputHistory] using actual

end Counting.HardnessEncoded
