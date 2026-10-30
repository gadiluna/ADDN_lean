import Counting.ExternalFiniteConstraints
import Counting.StackEmitTemplates
import Counting.StackDescendingEmit

namespace Counting.External.CookLevin.StackGenerator
open StackMachine.Routine FiniteConstraints

/-- A fixed-alphabet cell template: one positive clause and all ordered
pairs of distinct negative literals, exactly as in `FiniteConstraints.oneHot`. -/
def oneHotTemplate (alphabet : Nat) : List (List (Nat × Bool)) :=
  [(List.finRange alphabet).map (fun value => (value.val,true))]++
    (List.finRange alphabet).flatMap (fun first =>
      ((List.finRange alphabet).filter (fun second => second ≠ first)).map
        (fun second => [(first.val,false),(second.val,false)]))

theorem finRange_values (count : Nat) : (List.finRange count).map Fin.val = List.range count := by
  apply List.ext_getElem <;> simp

theorem oneHot_raw (cells alphabet : Nat) :
    (oneHot cells alphabet).map (List.map CNFEncoding.literalRaw) =
      (List.range cells).flatMap (fun cell => shiftedClauses (alphabet*cell) (oneHotTemplate alphabet)) := by
  rw [← finRange_values cells]
  simp only [oneHot,List.map_flatMap,List.flatMap_map]
  apply congrArg (List.flatMap · (List.finRange cells))
  funext cell
  simp [oneHotTemplate,shiftedClauses,shiftedLiterals,List.map_flatMap,List.map_map,
    CNFEncoding.literalRaw,lit,bitIndex,finProdFinEquiv,Nat.add_comm,Function.comp_def]

theorem sequence_flatMap {α : Type} (codec : Encoding.Codec α) (values : List α) :
    Encoding.sequence codec values = values.flatMap codec.encode := by
  induction values with
  | nil => rfl
  | cons value values ih => simp only [Encoding.sequence,List.flatMap_cons,ih]

theorem oneHot_encoded_chunks (cells alphabet : Nat) :
    emittedChunks (fun cell => Encoding.sequence clauseCodec
      (shiftedClauses (alphabet*cell) (oneHotTemplate alphabet))) cells =
        Encoding.sequence clauseCodec ((oneHot cells alphabet).map (List.map CNFEncoding.literalRaw)) := by
  rw [oneHot_raw]
  simp only [emittedChunks,sequence_flatMap,List.flatMap_assoc]

end Counting.External.CookLevin.StackGenerator
