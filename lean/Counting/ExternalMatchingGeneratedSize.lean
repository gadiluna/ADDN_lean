import Counting.ExternalMatchingGenerator
import Counting.ExternalMatchingSerialization
import Counting.ExternalThreeSATTyped

namespace Counting.External.MatchingMachine

theorem matchingRows_coordinates {n m : Nat} (formula : ThreeSAT n m) :
    matchingRows n (formula.toCNF.map (List.map CNFEncoding.literalRaw))=formula.sparseRawRows := by
  unfold matchingRows
  simp only [List.length_map,ThreeSAT.toCNF,List.length_finRange]
  change variableBlocksRows 0 (ThreeSAT.slotCount n m) (3*m) n++
    clauseRows (ThreeSAT.slotCount n m) (3*m+1) (ThreeSAT.slotCount n m) 0
      (formula.toCNF.map (List.map CNFEncoding.literalRaw))++
    completionRows (ThreeSAT.slotCount n m+m) (ThreeSAT.slotCount n m+m) (2*ThreeSAT.slotCount n m)
      (ThreeSAT.slotCount n m-m)=_
  rw [variableBlocksRows_coordinates,clauseRows_coordinates,completionRows_coordinates,formula.sparseRawRows_blocks]

theorem matchingRows_typed (input : CNFInput) (three : ∀ clause∈input.2,clause.length=3) :
    matchingRows input.1 (CNFEncoding.toRaw input).2=(CNFMachine.asThreeSAT input three).sparseRawRows := by
  have equal := matchingRows_coordinates (CNFMachine.asThreeSAT input three)
  simpa only [CNFMachine.asThreeSAT_toCNF,CNFEncoding.toRaw] using equal

theorem matchingRows_length (input : CNFInput) (three : ∀ clause∈input.2,clause.length=3) :
    (matchingRows input.1 (CNFEncoding.toRaw input).2).length=MatchingDimensions.edges input.1 input.2.length := by
  rw [matchingRows_typed input three,ThreeSAT.sparseRawRows,List.length_map,ThreeSAT.sparseEdges_length]
  rfl

theorem rawRows_stream_length {q : Nat} (edges : List (MatchingEdge q)) :
    (Encoding.sequence (Encoding.list Encoding.natural)
      (edges.map (fun edge=>[edge.1.val,edge.2.1.val,edge.2.2.val]))).length≤edges.length*(6*q+8) := by
  induction edges with
  | nil => simp [Encoding.sequence]
  | cons edge rest ih =>
    have a := natural_length_le edge.1.val
    have b := natural_length_le edge.2.1.val
    have c := natural_length_le edge.2.2.val
    have x := edge.1.isLt
    have y := edge.2.1.isLt
    have z := edge.2.2.isLt
    have header : (Encoding.natural.encode 3).length=5 := rfl
    simp only [List.map_cons,Encoding.sequence,Encoding.list,List.length_cons,List.length_nil,List.length_append,
      Nat.reduceAdd,header,List.length_nil,Nat.add_zero]
    simp only [Encoding.list] at ih
    nlinarith

theorem matchingRows_stream_length (input : CNFInput) (three : ∀ clause∈input.2,clause.length=3) :
    (Encoding.sequence (Encoding.list Encoding.natural) (matchingRows input.1 (CNFEncoding.toRaw input).2)).length≤
      MatchingDimensions.edges input.1 input.2.length*(6*MatchingDimensions.order input.1 input.2.length+8) := by
  rw [matchingRows_typed input three]
  have bound := rawRows_stream_length (CNFMachine.asThreeSAT input three).sparseEdges
  rw [ThreeSAT.sparseEdges_length] at bound
  exact bound

theorem matchingGenerator_output_eq (input : CNFInput) (three : ∀ clause∈input.2,clause.length=3) :
    (Encoding.list Encoding.boolean).encode (List.replicate (MatchingDimensions.order input.1 input.2.length) true)++
      Encoding.natural.encode (MatchingDimensions.edges input.1 input.2.length)++
        Encoding.sequence (Encoding.list Encoding.natural) (matchingRows input.1 (CNFEncoding.toRaw input).2)=
      ThreeDMEncoding.codec.encode (CNFMachine.asThreeSAT input three).sparseInput := by
  change _=ThreeDMEncoding.rawCodec.encode (ThreeDMEncoding.toRaw _)
  rw [ThreeSAT.sparseInput_toRaw]
  rw [matchingRows_typed input three]
  simp only [ThreeDMEncoding.rawCodec,Encoding.product,Encoding.list,ThreeSAT.sparseRawRows,List.length_map,ThreeSAT.sparseEdges_length]
  exact List.append_assoc _ _ _

end Counting.External.MatchingMachine
