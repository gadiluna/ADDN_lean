import Counting.StackRealizabilityRoundData

namespace Counting.StackMachine.RealizabilityCheck

/-- A binary input-size bound, with an explicit finite node table. -/
def roundSize (nodes : List Executable.Node) (values : List Nat) (order round : Nat) : Nat :=
  massInputSize nodes values+order.size+round.size+nodes.length+4

theorem roundSize_positive (nodes : List Executable.Node) (values : List Nat) (order round : Nat) :
    1 ≤ roundSize nodes values order round := by unfold roundSize;omega

theorem roundVisibleValue_size (nodes : List Executable.Node) (values : List Nat) (round : Nat) :
    (roundVisibleValue nodes values round).size ≤ massInputSize nodes values := by
  have bounded := levelRangeSum_size nodes (round+1) 0 0 values
  simp only [Nat.zero_add,Nat.size_zero] at bounded
  have sequenceSmall : (Encoding.sequence Encoding.natural values).length ≤ massInputSize nodes values := by
    change _ ≤ ((Encoding.list Encoding.node).encode nodes).length+
      (Encoding.natural.encode values.length++Encoding.sequence Encoding.natural values).length+1
    simp only [List.length_append]
    omega
  exact bounded.trans sequenceSmall

theorem roundComputedTables_size (nodes : List Executable.Node) (values : List Nat) (order round : Nat)
    (width : List Bool) (counted : width.length=nodes.length+1) :
    graphSize (roundComputedTables nodes values order round) width=
      7*(nodes.length+1)+2*(nodes.length+1)^2+1 := by
  simp [graphSize,roundComputedTables,counted]
  ring

theorem roundMasks_scale (size : Nat) :
    12000*(2*size)^5=384000*size^5 := by ring

theorem roundPoint_scale (size : Nat) :
    300000000*(4*size)^16=1288490188800000000*size^16 := by ring

theorem roundGraph_scale (size : Nat) :
    30000000000*(10*size^2)^12=30000000000000000000000*size^24 := by ring

end Counting.StackMachine.RealizabilityCheck
