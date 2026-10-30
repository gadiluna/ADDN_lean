import Counting.StackRealizabilityMaskSlots
import Counting.RealizabilityCompactFields

namespace Counting.StackMachine.RealizabilityCheck
open RealizabilityVerifier

theorem nodeMask_bitAt (vista : Executable.Vista) (predicate : Executable.Node → Bool)
    (slot : CompactGraph.Slot vista) :
    BitGraph.bitAt (vista.nodes.toList.map predicate++[false]) slot.val=
      (decide (slot.val<vista.nodes.size) && predicate (vista.node slot.val)):=by
  by_cases inside : slot.val<vista.nodes.size
  · unfold BitGraph.bitAt
    rw [List.getElem?_append_left (by simpa using inside),List.getElem?_map]
    simp [Executable.Vista.node,inside]
  · have last : slot.val=vista.nodes.size:=by have bound:=slot.isLt;omega
    unfold BitGraph.bitAt
    rw [List.getElem?_append_right (by simp [last])]
    simp [last]

theorem maskSlots_old (vista : Executable.Vista) (round : Nat) (slot : CompactGraph.Slot vista) :
    BitGraph.bitAt (vista.nodes.toList.map (fun node=>decide (node.level=round))++[false]) slot.val=
      CompactGraph.isOld vista round slot:=by
  rw [nodeMask_bitAt]
  simp [CompactGraph.isOld]

theorem maskSlots_new (vista : Executable.Vista) (round : Nat) (slot : CompactGraph.Slot vista) :
    BitGraph.bitAt (vista.nodes.toList.map (fun node=>decide (node.level=round+1))++[false]) slot.val=
      CompactGraph.isNew vista round slot:=by
  rw [nodeMask_bitAt]
  simp [CompactGraph.isNew]

theorem maskSlots_degree (vista : Executable.Vista) (slot : CompactGraph.Slot vista) :
    BitGraph.bitAt (vista.nodes.toList.map (fun node=>decide (0<node.degree))++[false]) slot.val=
      decide (0<(vista.node slot.val).degree):=by
  rw [nodeMask_bitAt]
  by_cases inside : slot.val<vista.nodes.size
  · simp [inside]
  · have missing : vista.nodes[slot.val]?=none:=Array.getElem?_eq_none (by omega)
    simp [inside,Executable.Vista.node]
    rfl

end Counting.StackMachine.RealizabilityCheck
