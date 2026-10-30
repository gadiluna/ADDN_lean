import Counting.AuditPropagationLevelOrder
import Counting.PropagationEncodingBounds

namespace Counting.StackMachine.AuditPropagation

/-- Every prefix of a level scan has a quadratic complete encoding bound.
All writes target level r, hence none changes a child at level r+1. -/
theorem levelScan_encoded_bound (vista : Executable.Vista) (r start count : Nat) (weights : Array Nat)
    (sized : weights.size=vista.nodes.size) (inside : start+count ≤ vista.nodes.size) :
    ((Encoding.array Encoding.natural).encode (levelScan vista r start count weights)).length ≤
      8*(((Encoding.array Encoding.natural).encode weights).length+1)^2 := by
  let L := ((Encoding.array Encoding.natural).encode weights).length
  let indices := (List.range' start count).filter (fun i=>(vista.node i).level==r)
  have distinct : indices.Nodup := (List.nodup_range' (s:=start) (n:=count)).filter _
  have atLevel (i : Nat) (member : i∈indices) : i∈Executable.levelNodes vista r := by
    obtain ⟨inRange,selected⟩ := List.mem_filter.mp member
    have range := List.mem_range'.mp inRange
    apply (Executable.mem_levelNodes vista r i).mpr
    exact ⟨by omega,by simpa using selected⟩
  have values (i : Nat) : weights[i]?.getD 0 ≤ 2^L :=
    Nat.le_of_lt (Nat.size_le.mp (Encoding.naturalArray_entry_size_le weights i))
  have bits (i : Nat) : ((levelScan vista r start count weights)[i]?.getD 0).size ≤
      L+1+(vista.nodes.size+1).size := by
    rw [levelScan_eq_updateNodes]
    have bound := Executable.updateNodes_value_bound vista r indices weights sized distinct atLevel (2^L) values i
    have high : 2^L*(vista.nodes.size+1) < 2^(L+1+(vista.nodes.size+1).size) := by
      calc
        _ < 2^(L+1)*(vista.nodes.size+1) := Nat.mul_lt_mul_of_pos_right (Nat.pow_lt_pow_right (by decide) (by omega)) (by omega)
        _ ≤ 2^(L+1)*2^(vista.nodes.size+1).size := Nat.mul_le_mul_left _ (Nat.le_of_lt (Nat.lt_size_self _))
        _ = _ := (pow_add _ _ _).symm
    exact Nat.size_le.mpr (bound.trans_lt high)
  have total := Encoding.naturalArray_length_le_bitWidth (levelScan vista r start count weights)
    (L+1+(vista.nodes.size+1).size) (by
      intro value member
      obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp member
      have inArray : i<(levelScan vista r start count weights).size := by simpa using hi
      simpa [Array.getElem?_eq_getElem inArray,←eq] using bits i)
  rw [levelScan_size,sized] at total
  have countBound := Encoding.array_size_le_length Encoding.natural weights
    (by intro value _;rw [Encoding.natural_length];omega)
  change weights.size ≤ L at countBound
  rw [sized] at countBound
  have sizeN : vista.nodes.size.size ≤ vista.nodes.size := Nat.size_le.mpr Nat.lt_two_pow_self
  have sizeNext : (vista.nodes.size+1).size ≤ vista.nodes.size+1 := Nat.size_le.mpr Nat.lt_two_pow_self
  have payload := Nat.mul_le_mul countBound
    (show 2*(L+1+(vista.nodes.size+1).size)+1 ≤ 4*L+5 by omega)
  change _ ≤ 8*(L+1)^2
  nlinarith only [total,payload,sizeN,countBound,Nat.zero_le L]

end Counting.StackMachine.AuditPropagation
