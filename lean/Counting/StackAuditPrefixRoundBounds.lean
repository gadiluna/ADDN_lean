import Counting.StackAuditPrefixRound

namespace Counting.StackMachine.AuditPrefix
open Routine
set_option backward.isDefEq.respectTransparency false

/-- During the bounded scan every generated label is bounded by the
actual serialized node count. The candidate contributes only its binary
length, not its numerical value. -/
theorem prefixRound_budget (vista : Executable.Vista) (leaders candidate last level : Nat)
    (before : level<last) (fits : last≤vista.nodes.size) (anchor : Option Nat)
    (saved : ∀ value∈anchor,value≤level) :
    3000000*((Encoding.sequence Encoding.node vista.nodes.toList++
      Encoding.natural.encode vista.bottom).length+level.size+(level+1).size+
        candidate.size+(anchorCode anchor).size+1)^6 ≤
      50000000000*((inputWord vista leaders candidate last).length+1)^6 := by
  have tableLength : (Encoding.sequence Encoding.node vista.nodes.toList++
      Encoding.natural.encode vista.bottom).length≤(Encoding.vista.encode vista).length := by
    change _≤(Encoding.natural.encode vista.nodes.size++Encoding.sequence Encoding.node vista.nodes.toList++
      Encoding.natural.encode vista.bottom).length
    simp only [List.length_append];omega
  have nodes:=Encoding.vista_nodes_le_length vista
  have inputLength:=inputWord_length vista leaders candidate last
  have levelSize : level.size≤level:=Nat.size_le.mpr Nat.lt_two_pow_self
  have nextSize : (level+1).size≤level+1:=Nat.size_le.mpr Nat.lt_two_pow_self
  have anchorSize : (anchorCode anchor).size≤anchorCode anchor:=Nat.size_le.mpr Nat.lt_two_pow_self
  have anchorBound:=anchorCode_le saved
  have base : (Encoding.sequence Encoding.node vista.nodes.toList++
      Encoding.natural.encode vista.bottom).length+level.size+(level+1).size+
        candidate.size+(anchorCode anchor).size+1≤5*((inputWord vista leaders candidate last).length+1) := by omega
  have raised:=Nat.mul_le_mul_left 3000000 (Nat.pow_le_pow_left base 6)
  have factor : 3000000*(5*((inputWord vista leaders candidate last).length+1))^6=
      46875000000*((inputWord vista leaders candidate last).length+1)^6 := by ring
  rw [factor] at raised
  exact raised.trans (Nat.mul_le_mul_right _ (by decide))

theorem prefixRound_bounded (vista : Executable.Vista) (valid : vista.valid=true)
    (leaders candidate last level : Nat) (depth : last≤(vista.node vista.bottom).level)
    (before : level<last) (fits : last≤vista.nodes.size)
    (remaining : List Bool) (accepted : Bool) (anchor : Option Nat)
    (saved : ∀ value∈anchor,value≤level) :
    ∃ time ≤ 50000000000*((inputWord vista leaders candidate last).length+1)^6,
      Executes prefixRound (roundFile vista leaders candidate last level remaining accepted anchor) time
        (roundFile vista leaders candidate last (level+1) remaining
          (accepted && roundCheck vista candidate level) (nextAnchor vista level anchor)) := by
  obtain ⟨time,bound,run⟩:=prefixRound_executes vista valid leaders candidate last level (by omega)
    remaining accepted anchor
  exact ⟨time,bound.trans (prefixRound_budget vista leaders candidate last level before fits anchor saved),run⟩

end Counting.StackMachine.AuditPrefix
