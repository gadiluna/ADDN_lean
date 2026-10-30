import Counting.StackAnchorMatrixComplete
import Counting.StackAnchorMatrixBounds
import Counting.StackAnchorLeaderBounds

namespace Counting.StackMachine.AnchorMatrix
set_option maxHeartbeats 2000000

theorem generatedRows_length (nodes remaining : List Executable.Node) (anchor previous start : Nat) :
    (generatedRows nodes anchor previous start remaining).length ≤ remaining.length := by
  induction remaining generalizing start with
  | nil => simp [generatedRows]
  | cons node rest ih =>
    have bound:=ih (start+1)
    simp only [generatedRows]
    split
    · simpa only [List.length_cons] using Nat.add_le_add_right bound 1
    · exact bound.trans (by simp)

theorem generatedRows_member (nodes remaining : List Executable.Node) (anchor previous start : Nat)
    (row : List Rat) (member : row∈generatedRows nodes anchor previous start remaining) :
    ∃ query,row=AnchorCoefficient.flowRow nodes anchor query := by
  induction remaining generalizing start with
  | nil => simp [generatedRows] at member
  | cons node rest ih =>
    simp only [generatedRows] at member
    split at member
    · rcases List.mem_cons.mp member with equal|inside
      · exact ⟨start,equal⟩
      · exact ih (start+1) inside
    · exact ih (start+1) member

private theorem sequence_length_bound {α : Type} (codec : Encoding.Codec α) (values : List α) (bound : Nat)
    (bounded : ∀ value∈values,(codec.encode value).length ≤ bound) :
    (Encoding.sequence codec values).length ≤ values.length*bound := by
  induction values with
  | nil => simp [Encoding.sequence]
  | cons value values ih =>
    have head := bounded value (by simp)
    have rest := ih (by intro x member;exact bounded x (List.mem_cons_of_mem value member))
    simp only [Encoding.sequence,List.length_append,List.length_cons]
    nlinarith

theorem producedRows_length (nodes : List Executable.Node) (anchor previous leaders : Nat) :
    (producedRows nodes anchor previous leaders).length ≤ nodes.length+1 := by
  have bound := generatedRows_length nodes nodes anchor previous 0
  simpa only [producedRows,List.length_append,List.length_singleton] using Nat.add_le_add_right bound 1

theorem matrix_stream_length (nodes : List Executable.Node) (anchor previous leaders limit : Nat)
    (inputBound : (Encoding.sequence Encoding.node nodes).length ≤ limit) :
    (Encoding.sequence (Encoding.framed Encoding.rationalRow) (producedRows nodes anchor previous leaders)).length ≤
      10001*(limit+leaders.size+1)^3 := by
  let size := limit+leaders.size+1
  have one : 1 ≤ size := by dsimp only [size];omega
  have count := (AnchorRow.nodes_length nodes).trans inputBound
  have rows := producedRows_length nodes anchor previous leaders
  have countSize : (producedRows nodes anchor previous leaders).length ≤ size := by dsimp only [size];omega
  have limitSize : limit+1 ≤ size := by dsimp only [size];omega
  have bounded : ∀ row∈producedRows nodes anchor previous leaders,
      ((Encoding.framed Encoding.rationalRow).encode row).length ≤ 10000*size^2+1 := by
    intro row member
    rw [Encoding.framed_length]
    rcases List.mem_append.mp member with flow|last
    · obtain ⟨query,rfl⟩ := generatedRows_member nodes nodes anchor previous 0 row flow
      have bound := (flowRow_length nodes query anchor limit inputBound).trans
        (Nat.mul_le_mul_left 5000 (Nat.pow_le_pow_left limitSize 2))
      omega
    · have equal := List.mem_singleton.mp last
      subst row
      have bound := AnchorLeaderRow.row_length nodes leaders anchor limit inputBound
      change _ ≤ 30*size^2 at bound
      omega
  have stream := sequence_length_bound (Encoding.framed Encoding.rationalRow)
    (producedRows nodes anchor previous leaders) _ bounded
  have raised := stream.trans (Nat.mul_le_mul_right _ countSize)
  have linear : size ≤ size^3 := Nat.le_self_pow (by decide) _
  change _ ≤ 10001*size^3
  nlinarith only [raised,linear]

theorem matrix_length (nodes : List Executable.Node) (anchor previous leaders limit : Nat)
    (inputBound : (Encoding.sequence Encoding.node nodes).length ≤ limit) :
    (Encoding.rationalMatrix.encode (producedRows nodes anchor previous leaders)).length ≤
      10004*(limit+leaders.size+1)^3 := by
  have stream := matrix_stream_length nodes anchor previous leaders limit inputBound
  have count := (AnchorRow.nodes_length nodes).trans inputBound
  have rows := producedRows_length nodes anchor previous leaders
  have bits : (producedRows nodes anchor previous leaders).length.size ≤
      (producedRows nodes anchor previous leaders).length := Nat.size_le.mpr Nat.lt_two_pow_self
  let size := limit+leaders.size+1
  have one : 1 ≤ size := by dsimp only [size];omega
  have rowBound : (producedRows nodes anchor previous leaders).length ≤ size := by dsimp only [size];omega
  have linear : size ≤ size^3 := Nat.le_self_pow (by decide) _
  change (Encoding.natural.encode (producedRows nodes anchor previous leaders).length++
    Encoding.sequence (Encoding.framed Encoding.rationalRow) (producedRows nodes anchor previous leaders)).length ≤ _
  rw [List.length_append,Encoding.natural_length]
  change _ ≤ 10004*size^3
  change _ ≤ 10001*size^3 at stream
  omega

theorem leaderBudget_polynomial (nodes : List Executable.Node) (anchor previous leaders limit : Nat)
    (suffix : List Bool) (tableBound : (Encoding.sequence Encoding.node nodes++suffix).length ≤ limit) :
    leaderBudget nodes anchor leaders suffix nodes.length.bits suffix ≤
      61000000*(limit+anchor.size+previous.size+leaders.size+1)^6 := by
  have table : (Encoding.sequence Encoding.node nodes).length ≤ limit := by
    simp only [List.length_append] at tableBound;omega
  have count := (AnchorRow.nodes_length nodes).trans table
  have countBits : nodes.length.size ≤ nodes.length := Nat.size_le.mpr Nat.lt_two_pow_self
  have suffixBound : suffix.length ≤ limit := by simp only [List.length_append] at tableBound;omega
  have rowCost := AnchorLeaderRow.rowBudget_polynomial nodes leaders anchor
    (Encoding.sequence Encoding.node nodes++suffix).length (by simp only [List.length_append];omega)
  have rowLength := AnchorLeaderRow.row_length nodes leaders anchor limit table
  let size := limit+anchor.size+previous.size+leaders.size+1
  have one : 1 ≤ size := by dsimp only [size];omega
  have base : (Encoding.sequence Encoding.node nodes++suffix).length+leaders.size+anchor.size+1 ≤ size := by
    dsimp only [size];omega
  have lengthBase : limit+leaders.size+1 ≤ size := by dsimp only [size];omega
  have raisedCost := rowCost.trans (Nat.mul_le_mul_left 300000 (Nat.pow_le_pow_left base 4))
  have raisedLength := rowLength.trans (Nat.mul_le_mul_left 30 (Nat.pow_le_pow_left lengthBase 2))
  have squared : 1 ≤ size^2 := Nat.one_le_pow _ _ one
  have headerBase : (Encoding.rationalRow.encode (AnchorCoefficient.leaderRow nodes anchor leaders)).length+1 ≤ 31*size^2 := by omega
  have headerBound := Nat.mul_le_mul_left 2000 (Nat.pow_le_pow_left headerBase 3)
  have headerRaised : 2000*((Encoding.rationalRow.encode (AnchorCoefficient.leaderRow nodes anchor leaders)).length+1)^3 ≤
      59582000*size^6 := by nlinarith only [headerBound]
  have linear : size ≤ size^6 := Nat.le_self_pow (by decide) _
  have square : size^2 ≤ size^6 := Nat.pow_le_pow_right one (by decide)
  have fourth : size^4 ≤ size^6 := Nat.pow_le_pow_right one (by decide)
  have labels : limit+leaders.size ≤ size := by dsimp only [size];omega
  unfold leaderBudget
  rw [Encoding.bits_length]
  change _ ≤ 61000000*size^6
  omega

theorem buildBudget_polynomial (nodes : List Executable.Node) (anchor previous leaders limit : Nat)
    (suffix : List Bool) (tableBound : (Encoding.sequence Encoding.node nodes++suffix).length ≤ limit) :
    buildBudget nodes anchor previous leaders suffix ≤
      100000000*(limit+anchor.size+previous.size+leaders.size+1)^6 := by
  have table : (Encoding.sequence Encoding.node nodes).length ≤ limit := by
    simp only [List.length_append] at tableBound;omega
  have count := (AnchorRow.nodes_length nodes).trans table
  have rows := producedRows_length nodes anchor previous leaders
  have stream := matrix_stream_length nodes anchor previous leaders limit table
  have outer := loopBudget_polynomial nodes anchor previous limit suffix tableBound
  have leader := leaderBudget_polynomial nodes anchor previous leaders limit suffix tableBound
  let size := limit+anchor.size+previous.size+leaders.size+1
  have one : 1 ≤ size := by dsimp only [size];omega
  have base : limit+anchor.size+previous.size+1 ≤ size := by dsimp only [size];omega
  have streamBase : limit+leaders.size+1 ≤ size := by dsimp only [size];omega
  have outerRaised := outer.trans (Nat.mul_le_mul_left 9000000 (Nat.pow_le_pow_left base 5))
  have streamRaised := stream.trans (Nat.mul_le_mul_left 10001 (Nat.pow_le_pow_left streamBase 3))
  have rowBound : (producedRows nodes anchor previous leaders).length ≤ size := by dsimp only [size];omega
  have squareBound := Nat.mul_le_mul rowBound (Nat.add_le_add_right rowBound 1)
  have linear : size ≤ size^6 := Nat.le_self_pow (by decide) _
  have square : size^2 ≤ size^6 := Nat.pow_le_pow_right one (by decide)
  have cubic : size^3 ≤ size^6 := Nat.pow_le_pow_right one (by decide)
  have fifth : size^5 ≤ size^6 := Nat.pow_le_pow_right one (by decide)
  unfold buildBudget
  change _ ≤ 100000000*size^6
  change _ ≤ 61000000*size^6 at leader
  nlinarith only [outerRaised,streamRaised,rowBound,squareBound,linear,square,cubic,fifth,one,leader]

end Counting.StackMachine.AnchorMatrix
