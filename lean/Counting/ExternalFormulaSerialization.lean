import Counting.ExternalInitialAdjacent
import Counting.ExternalTableau
import Counting.ExternalOneHotLayout

namespace Counting.External.CookLevin.StackGenerator
open Tableau FiniteConstraints InitialRows StackMachine.Routine

/-- Exact list order of the five blocks emitted by the tableau generator.
This is an equality of clauses, not merely equisatisfiability. -/
theorem formula_raw_blocks {time width : Nat} (setup : Setup width) (program : Machine.Program)
    (dynamics : Dynamics width (Cellular.alphabet program)) :
    (Tableau.formula (T := time) dynamics (setup.constraints program) (Cellular.accept program)).map
      (List.map CNFEncoding.literalRaw) =
      (oneHot ((time+1)*width) (Cellular.alphabet program)).map (List.map CNFEncoding.literalRaw)++
      (List.finRange width).flatMap (fun place =>
        ((initialConstraint (T := time) (setup.unary program place)).toCNF).map (List.map CNFEncoding.literalRaw))++
      (List.finRange (setup.capacity-1)).flatMap (fun i =>
        ((initialConstraint (T := time) (setup.binary program
          (adjacentLeft setup.capacity i) (adjacentRight setup.capacity i))).toCNF).map (List.map CNFEncoding.literalRaw))++
      (List.finRange time).flatMap (fun round => (List.finRange width).flatMap (fun place =>
        ((transitionConstraint dynamics round place).toCNF).map (List.map CNFEncoding.literalRaw)))++
      [(finalClause (T := time) (w := width) (Cellular.accept program)).map CNFEncoding.literalRaw] := by
  rw [Tableau.formula,FiniteConstraints.toCNF,Tableau.constraints,setup.constraints_adjacent]
  simp only [List.map_append,List.map_cons,List.map_nil,List.flatMap_append,List.map_map,
    List.flatMap_map,List.map_flatMap,List.flatMap_assoc,List.append_assoc,Function.comp_def]

/-- No extra list header is inserted between blocks. The last singleton
contributes exactly its clause encoding, including that clause's own header. -/
theorem formula_encoded_blocks {time width : Nat} (setup : Setup width) (program : Machine.Program)
    (dynamics : Dynamics width (Cellular.alphabet program)) :
    Encoding.sequence clauseCodec
      ((Tableau.formula (T := time) dynamics (setup.constraints program) (Cellular.accept program)).map
        (List.map CNFEncoding.literalRaw)) =
      Encoding.sequence clauseCodec
        ((oneHot ((time+1)*width) (Cellular.alphabet program)).map (List.map CNFEncoding.literalRaw))++
      (List.finRange width).flatMap (fun place => Encoding.sequence clauseCodec
        (((initialConstraint (T := time) (setup.unary program place)).toCNF).map (List.map CNFEncoding.literalRaw)))++
      (List.finRange (setup.capacity-1)).flatMap (fun i => Encoding.sequence clauseCodec
        (((initialConstraint (T := time) (setup.binary program
          (adjacentLeft setup.capacity i) (adjacentRight setup.capacity i))).toCNF).map (List.map CNFEncoding.literalRaw)))++
      (List.finRange time).flatMap (fun round => (List.finRange width).flatMap (fun place =>
        Encoding.sequence clauseCodec
          (((transitionConstraint dynamics round place).toCNF).map (List.map CNFEncoding.literalRaw))))++
      clauseCodec.encode ((finalClause (T := time) (w := width) (Cellular.accept program)).map CNFEncoding.literalRaw) := by
  rw [formula_raw_blocks]
  simp only [sequence_flatMap,List.flatMap_append,List.flatMap_assoc,List.flatMap_cons,
    List.flatMap_nil,List.append_nil]

/-- The outer CNF codec adds exactly the explicit variable table and one
clause-count header to the serialized clause stream. -/
theorem formula_codec_header {variableCount : Nat} (formula : CNF variableCount) :
    CNFEncoding.codec.encode ⟨variableCount,formula⟩ =
      (Encoding.list Encoding.boolean).encode (List.replicate variableCount true)++
      Encoding.natural.encode formula.length++
      Encoding.sequence clauseCodec (formula.map (List.map CNFEncoding.literalRaw)) := by
  simp only [CNFEncoding.codec,Encoding.transport,CNFEncoding.toRaw,CNFEncoding.rawCodec,
    Encoding.product,Encoding.list,List.length_map,List.append_assoc]

end Counting.External.CookLevin.StackGenerator
