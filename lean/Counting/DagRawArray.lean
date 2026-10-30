import Counting.DagRawPhysical
import Counting.EncodingTabulateBounds

namespace Counting.Encoding
open Executable

/-- One physical round reads the old array for every receiver and creates
a separate new array. Zero arcs produce no received bundle. -/
def rawRound (leaders : Array Bool) (graph : Simulation.RoundGraph) (previous : Array Vista) : Array Vista :=
  let states := fun sender : Fin leaders.size =>
    (previous[sender.val]?).getD (initialVista leaders[sender.val])
  Array.ofFn (fun receiver : Fin leaders.size =>
    rawUpdate (states receiver)
      (senderBundles (List.finRange leaders.size) (matrixEdge graph leaders.size) states receiver)
      (((List.finRange leaders.size).map
        (fun target => matrixEdge graph leaders.size receiver target)).sum))

theorem rawInputVistaArrayRun_succ_listed (input : Simulation.Input) (depth : Nat)
    (within : depth < input.rounds.size) :
    rawInputVistaArrayRun input (depth+1) =
      rawRound input.leaders input.rounds[depth] (rawInputVistaArrayRun input depth) := by
  have graph := inputGraph_listed input ⟨depth, within⟩
  simp only [rawInputVistaArrayRun, graph, rawRound, inputLeader]

theorem rawInputVistaArrayRun_initial (input : Simulation.Input) :
    rawInputVistaArrayRun input 0 = input.leaders.map initialVista := by
  change Array.ofFn (fun i : Fin input.leaders.size => initialVista input.leaders[i.val]) = _
  have mapped := Array.map_ofFn (f := fun i : Fin input.leaders.size => input.leaders[i.val])
    (g := initialVista)
  simpa only [Array.ofFn_getElem, Function.comp_def] using mapped.symm

theorem rawInputVistaArrayRun_fold (input : Simulation.Input) (depth : Nat)
    (within : depth ≤ input.rounds.size) :
    rawInputVistaArrayRun input depth =
      (input.rounds.toList.take depth).foldl (fun states graph => rawRound input.leaders graph states)
        (input.leaders.map initialVista) := by
  induction depth with
  | zero => simp only [List.take_zero, List.foldl_nil, rawInputVistaArrayRun_initial]
  | succ depth ih =>
      have inside : depth < input.rounds.size := by omega
      rw [rawInputVistaArrayRun_succ_listed input depth inside, ih (by omega)]
      rw [List.take_succ_eq_append_getElem (by simpa using inside)]
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, Array.getElem_toList]

theorem rawInputVistas_fold (input : Simulation.Input) :
    rawInputVistas input =
      input.rounds.foldl (fun states graph => rawRound input.leaders graph states)
        (input.leaders.map initialVista) := by
  rw [rawInputVistas, rawInputVistaArrayRun_fold input _ le_rfl]
  simp only [← Array.length_toList, List.take_length, Array.foldl_toList]

/-- The entire stored configuration, including its list header, remains
polynomial in the original input length at every physical prefix. -/
theorem rawInputVistaArrayRun_encoding_length (input : Simulation.Input) (depth : Nat)
    (within : depth ≤ input.rounds.size) :
    ((array vista).encode (rawInputVistaArrayRun input depth)).length ≤
      203*((networkInput.encode input).length+1)^6 := by
  rw [rawInputVistaArrayRun_eq]
  have bound := array_ofFn_length_le vista (rawInputVistaRun input depth)
    (200*((networkInput.encode input).length+1)^5)
    (rawInputVistaRun_encoding_length input depth within)
  let L := (networkInput.encode input).length
  have size : input.leaders.size.size ≤ L :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans (network_agents_le_length input)
  have count : input.leaders.size ≤ L := network_agents_le_length input
  have powerBound : L+1 ≤ (L+1)^6 := Nat.le_self_pow (by decide) _
  have payload : input.leaders.size*(200*(L+1)^5) ≤ 200*(L+1)^6 := by
    calc
      _ ≤ (L+1)*(200*(L+1)^5) := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by ring
  change _ ≤ 203*(L+1)^6
  change _ ≤ 2*input.leaders.size.size+1+input.leaders.size*(200*(L+1)^5) at bound
  omega

theorem rawInputVistas_array_encoding_length (input : Simulation.Input) :
    ((array vista).encode (rawInputVistas input)).length ≤
      203*((networkInput.encode input).length+1)^6 :=
  rawInputVistaArrayRun_encoding_length input _ le_rfl

end Counting.Encoding
