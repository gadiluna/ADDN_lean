import Counting.HardnessEncodedBounds

namespace Counting.HardnessEncoded.Tests
open Encoding
set_option maxRecDepth 4096

def noCover : X3C.Instance 2 0 where
  triples := Fin.elim0
  triple_card := by intro j; exact Fin.elim0 j
  distinct := by intro a; exact Fin.elim0 a

def covered : X3C.Instance 2 2 where
  triples j := if j.val = 0 then {0,1,2} else {3,4,5}
  triple_card := by intro j; fin_cases j <;> decide
  distinct := by intro a b; fin_cases a <;> fin_cases b <;> decide

private def require (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"Encoded hardness test failed: {label}")

private def check {q m : Nat} (inst : X3C.Instance q m) : IO Unit := do
  let actual := input inst
  require "population" (actual.leaders.size == X3C.baselineMass q m+1)
  require "round count" (actual.rounds.size == X3C.base q)
  require "one leader" (inputLeaderCount actual == 1)
  require "valid explicit network" (networkValid actual)
  require "binary network roundtrip" (decodeNetwork? (networkBits inst) == some actual)
  require "loopless matrices" (actual.rounds.all fun matrix =>
    (List.range actual.leaders.size).all fun i => (matrix[i]?.getD #[])[i]?.getD 1 == 0)
  let view := leaderVista inst
  require "valid actual leader DAG" view.valid
  require "leader DAG depth" ((view.node view.bottom).level == X3C.base q)
  require "binary vista roundtrip" (vistaInput.decodeExact (vistaBits inst) == some (view,1))

private def tests : IO Unit := do
  check noCover
  check covered
  IO.println "Encoded hardness tests passed (18 network/DAG checks on two X3C instances)."

#eval tests

theorem noCover_negative : ¬ ∃ chosen, noCover.IsExactCover chosen := by
  intro ⟨chosen, cover⟩
  have empty : chosen = ∅ := Finset.eq_empty_of_forall_notMem (fun a => Fin.elim0 a)
  have impossible := cover (0 : Fin 6)
  simp only [empty, Finset.filter_empty, Finset.card_empty] at impossible
  omega

theorem covered_positive : ∃ chosen, covered.IsExactCover chosen := by
  exact ⟨Finset.univ, by unfold X3C.Instance.IsExactCover; decide⟩

example : BinarySomeAgentKnows (networkBits noCover) := by
  rw [networkBits_correct noCover (by omega)]
  exact noCover_negative

example : ¬ BinarySomeAgentKnows (networkBits covered) := by
  rw [networkBits_correct covered (by omega)]
  exact not_not.mpr covered_positive

example : BinaryAtMostOneVista (vistaBits noCover) := by
  rw [vistaBits_correct noCover (by omega)]
  exact noCover_negative

example : ¬ BinaryAtMostOneVista (vistaBits covered) := by
  rw [vistaBits_correct covered (by omega)]
  exact not_not.mpr covered_positive

end Counting.HardnessEncoded.Tests
