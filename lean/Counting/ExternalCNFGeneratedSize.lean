import Counting.ExternalCNFFormulaSerialization
import Counting.ExternalCNFMeasureLoop

namespace Counting.External.CNFMachine
open StackMachine.Routine

theorem gateRows_length (current terminal count : Nat) (literals : List (Nat×Bool)) :
    (gateRows current terminal count literals).length=3*count := by
  induction count generalizing current literals with
  | zero => rfl
  | succ count ih => simp [gateRows,gateClauses,ih];omega

theorem clauseRows_length (current width : Nat) (literals : List (Nat×Bool)) :
    (clauseRows current width literals).length=3*width+2 := by simp [clauseRows,gateRows_length]

theorem formulaRows_length (current width : Nat) (clauses : List (List (Nat×Bool))) :
    (formulaRows current width clauses).length=clauses.length*(3*width+2) := by
  induction clauses generalizing current with
  | nil => simp [formulaRows]
  | cons clause rest ih => simp [formulaRows,clauseRows_length,ih];ring

theorem rawWidth_mapped {n : Nat} (formula : CNF n) :
    rawWidth (formula.map (List.map CNFEncoding.literalRaw))=formula.width := by
  induction formula with
  | nil => rfl
  | cons clause rest ih => simp [rawWidth,CNF.width,ih]

theorem rawWidth_member (clauses : List (List (Nat×Bool))) (clause : List (Nat×Bool))
    (member : clause∈clauses) : clause.length ≤ rawWidth clauses := by
  induction clauses with
  | nil => simp at member
  | cons first rest ih =>
    simp only [List.mem_cons] at member
    rcases member with rfl|member
    · simp [rawWidth]
    · have := ih member;dsimp [rawWidth];omega

theorem literal_sequence_length {n : Nat} (clause : List (Literal n)) :
    (Encoding.sequence literalCodec (clause.map CNFEncoding.literalRaw)).length ≤ clause.length*(2*n+2) := by
  induction clause with
  | nil => simp [Encoding.sequence]
  | cons literal rest ih =>
    have lit := literal_length_le literal.var.val literal.positive
    change (literalCodec.encode (CNFEncoding.literalRaw literal)).length ≤ 2*literal.var.val+2 at lit
    simp only [List.map_cons,Encoding.sequence,List.length_append,List.length_cons]
    have less := literal.var.isLt
    nlinarith

theorem threeClause_stream_length {n : Nat} (formula : CNF n)
    (three : ∀ clause∈formula,clause.length=3) :
    (Encoding.sequence (Encoding.list literalCodec) (formula.map (List.map CNFEncoding.literalRaw))).length ≤
      formula.length*(6*n+11) := by
  induction formula with
  | nil => simp [Encoding.sequence]
  | cons clause rest ih =>
    have len := three clause (by simp)
    have bound := literal_sequence_length clause
    rw [len] at bound
    have tailBound := ih (fun other member=>three other (by simp [member]))
    simp only [List.map_cons,Encoding.sequence,List.length_append,Encoding.list]
    have header : (Encoding.natural.encode clause.length).length=5 := by rw [len];rfl
    simp only [List.length_map,header,List.length_cons]
    change 5+(Encoding.sequence literalCodec (clause.map CNFEncoding.literalRaw)).length+
      (Encoding.sequence (Encoding.list literalCodec) (rest.map (List.map CNFEncoding.literalRaw))).length ≤ (rest.length+1)*(6*n+11)
    nlinarith

/-- The stream later reversed by the physical routine has a polynomial
length, independently of the runtime proof for producing that stream. -/
theorem generatedStream_length (input : CNFInput) :
    (Encoding.sequence (Encoding.list literalCodec)
      (formulaRows input.1 input.2.width (CNFEncoding.toRaw input).2)).length ≤
      (input.2.length*(3*input.2.width+2))*(6*input.2.targetVariables+11) := by
  have bound := threeClause_stream_length (reducedInput input).2 (reducedInput_three input)
  have raw := formulaRows_eq_reducedInput input.2
  have rows := congrArg Prod.snd raw
  change (reducedInput input).2.map (List.map CNFEncoding.literalRaw)=_ at rows
  rw [rows] at bound
  have count : (reducedInput input).2.length=input.2.length*(3*input.2.width+2) := by
    have equal := congrArg List.length rows
    simpa only [List.length_map,formulaRows_length] using equal
  rw [count] at bound
  exact bound

end Counting.External.CNFMachine
