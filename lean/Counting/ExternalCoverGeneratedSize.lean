import Counting.ExternalCoverGenerator
import Counting.ExternalMatchingCoverEncoding
import Counting.ExternalMatchingWitness

namespace Counting.External.CoverMachine

@[simp] theorem tripleRaw_eq {q : Nat} (triple : ThreeDMEncoding.Triple q) :
    ThreeDMEncoding.tripleRaw triple=[(triple 0).val,(triple 1).val,(triple 2).val] := rfl

theorem shiftedRows_coordinates (input : ThreeDMEncoding.Input) :
    shiftedRows input.1 (ThreeDMEncoding.toRaw input).2=
      ThreeDMEncoding.coverRows input.1 (ThreeDMEncoding.inputTriples input) := by
  simp only [shiftedRows,ThreeDMEncoding.toRaw,List.map_map,ThreeDMEncoding.coverRows]
  apply List.map_congr_left
  intro triple _member
  rw [Function.comp_apply,tripleRaw_eq]
  rfl

theorem coverRows_stream_length {q : Nat} (triples : List (ThreeDMEncoding.Triple q)) :
    (Encoding.sequence (Encoding.list Encoding.natural) (ThreeDMEncoding.coverRows q triples)).length≤ triples.length*(18*q+8) := by
  induction triples with
  | nil => simp [ThreeDMEncoding.coverRows,Encoding.sequence]
  | cons triple rest ih =>
    have a := MatchingMachine.natural_length_le (triple 0).val
    have b := MatchingMachine.natural_length_le (q+(triple 1).val)
    have c := MatchingMachine.natural_length_le (2*q+(triple 2).val)
    have x := (triple 0).isLt
    have y := (triple 1).isLt
    have z := (triple 2).isLt
    have header : (Encoding.natural.encode 3).length=5 := rfl
    simp only [ThreeDMEncoding.coverRows,List.map_cons,Encoding.sequence,Encoding.list,List.length_cons,List.length_nil,
      List.length_append,Nat.reduceAdd,header,Nat.add_zero]
    simp only [ThreeDMEncoding.coverRows,Encoding.list] at ih
    nlinarith

theorem shiftedRows_stream_length (input : ThreeDMEncoding.Input) :
    (Encoding.sequence (Encoding.list Encoding.natural) (shiftedRows input.1 (ThreeDMEncoding.toRaw input).2)).length≤
      input.2.1*(18*input.1+8) := by
  rw [shiftedRows_coordinates]
  simpa only [ThreeDMEncoding.inputTriples_length] using coverRows_stream_length (ThreeDMEncoding.inputTriples input)

theorem coverGenerator_output_eq (input : ThreeDMEncoding.Input) :
    (Encoding.list Encoding.boolean).encode (List.replicate (3*input.1) true)++
      Encoding.natural.encode input.2.1++
        Encoding.sequence (Encoding.list Encoding.natural) (shiftedRows input.1 (ThreeDMEncoding.toRaw input).2)=
      X3CEncoding.codec.encode (ThreeDMEncoding.coverInput input) := by
  change _=X3CEncoding.rawCodec.encode (X3CEncoding.toRaw _)
  rw [ThreeDMEncoding.coverInput_toRaw,shiftedRows_coordinates]
  simp only [X3CEncoding.rawCodec,Encoding.product,Encoding.list,ThreeDMEncoding.coverRows_length,ThreeDMEncoding.inputTriples_length]
  exact List.append_assoc _ _ _

theorem coverGeneratorCost_polynomial (length q m stream : Nat) (qBound : q≤ length) (mBound : m≤ length)
    (streamBound : stream≤ m*(18*q+8)) : coverGeneratorCost length q m stream≤100000*(length+1)^4 := by
  have streamLimit : stream≤ length*(18*length+8) := by
    apply streamBound.trans
    gcongr
  calc
    coverGeneratorCost length q m stream≤ coverGeneratorCost length length length (length*(18*length+8)) := by
      dsimp only [coverGeneratorCost,MatchingMachine.matchingFinalizeCost]
      gcongr
    _ ≤100000*(length+1)^4 := by
      dsimp only [coverGeneratorCost,MatchingMachine.matchingFinalizeCost]
      ring_nf
      omega

end Counting.External.CoverMachine
