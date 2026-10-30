import Counting.StackDagCanonicalCommitLoop
import Counting.EncodingArrayUpdateBounds
import Counting.DagUpdateSizeBounds
import Counting.DagImportPrefixBounds

namespace Counting.StackMachine.DagUpdate.Canonical
open Executable

theorem commitRecord_pool_payload (state : CanonicalState) (record : Sort.Record) :
    (Encoding.sequence Encoding.node (commitRecord state record).1.toList).length ≤
      (Encoding.sequence Encoding.node state.1.toList).length+(Sort.recordCodec.encode record).length := by
  unfold commitRecord intern
  split
  · exact Nat.le_add_right _ _
  · simp only [Array.toList_push,Encoding.sequence_length,List.map_append,List.sum_append,
      List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero]
    simp only [Sort.recordCodec,Encoding.product,List.length_append]
    omega

theorem commitFold_bounds (state : CanonicalState) (records : List Sort.Record) (width : Nat)
    (capacity : state.1.size+records.length ≤ width) :
    (records.foldl commitRecord state).1.size ≤ state.1.size+records.length ∧
    (Encoding.sequence Encoding.node (records.foldl commitRecord state).1.toList).length ≤
      (Encoding.sequence Encoding.node state.1.toList).length+(Encoding.sequence Sort.recordCodec records).length ∧
    ((Encoding.array Encoding.natural).encode (records.foldl commitRecord state).2).length ≤
      ((Encoding.array Encoding.natural).encode state.2).length+records.length*(2*width+1) := by
  induction records generalizing state with
  | nil => simp [Encoding.sequence]
  | cons record records ih =>
    have added := intern_size_le_succ state.1 record.2
    have nextCapacity : (commitRecord state record).1.size+records.length ≤ width := by
      simp only [List.length_cons] at capacity
      change (intern state.1 record.2).1.size+records.length ≤ width
      omega
    obtain ⟨count,payload,mapping⟩ := ih (commitRecord state record) nextCapacity
    have nodePayload := commitRecord_pool_payload state record
    have index := intern_index_lt state.1 record.2
    have bits : (intern state.1 record.2).2.size ≤ width :=
      (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by
        simp only [List.length_cons] at capacity
        omega)
    have replace := Encoding.naturalArray_setIfInBounds_length state.2 record.1 (intern state.1 record.2).2
    change ((Encoding.array Encoding.natural).encode (commitRecord state record).2).length ≤
      ((Encoding.array Encoding.natural).encode state.2).length+2*(intern state.1 record.2).2.size+1 at replace
    simp only [List.foldl_cons,List.length_cons,Encoding.sequence,List.length_append]
    change (records.foldl commitRecord (commitRecord state record)).1.size ≤ state.1.size+ (records.length+1) ∧ _
    have sizeNext : (commitRecord state record).1.size ≤ state.1.size+1 := added
    constructor
    · omega
    constructor
    · omega
    · nlinarith only [mapping,replace,bits]

def commitInputSize (state : CanonicalState) (records : List Sort.Record) (suffix : List Bool) : Nat :=
  ((Encoding.array Encoding.node).encode state.1).length+
    ((Encoding.array Encoding.natural).encode state.2).length+
    ((Encoding.list Sort.recordCodec).encode records).length+suffix.length+1

theorem record_positive_length (record : Sort.Record) : 1 ≤ (Sort.recordCodec.encode record).length := by
  simp only [Sort.recordCodec,Encoding.product,List.length_append,Encoding.natural_length]
  omega

theorem commitPrefix_encoded_bounds (state : CanonicalState) (records visited rest : List Sort.Record)
    (suffix : List Bool) (partition : visited++rest=records) :
    let next := visited.foldl commitRecord state
    ((Encoding.array Encoding.node).encode next.1).length ≤ 10*(commitInputSize state records suffix)^2 ∧
    ((Encoding.array Encoding.natural).encode next.2).length ≤ 10*(commitInputSize state records suffix)^2 := by
  let K := commitInputSize state records suffix
  let width := state.1.size+records.length
  have positive : 1 ≤ K := by dsimp [K,commitInputSize];omega
  have linear : K ≤ K^2 := Nat.le_self_pow (by decide) _
  have poolCount := Encoding.array_size_le_length Encoding.node state.1 (fun node _=>Encoding.node_positive_length node)
  have recordCount : records.length ≤ ((Encoding.list Sort.recordCodec).encode records).length := by
    simpa only [Encoding.array,Encoding.transport,List.toList_toArray,List.size_toArray] using
      Encoding.array_size_le_length Sort.recordCodec records.toArray (fun record _=>record_positive_length record)
  have countVisited : visited.length ≤ records.length := by rw [←partition,List.length_append];omega
  have widthBound : width ≤ K := by dsimp [width,K,commitInputSize];omega
  obtain ⟨count,payload,mapping⟩ := commitFold_bounds state visited width (by dsimp [width];omega)
  have encodedVisited : (Encoding.sequence Sort.recordCodec visited).length ≤
      ((Encoding.list Sort.recordCodec).encode records).length := by
    rw [←partition]
    simp only [Encoding.list,List.length_append,Encoding.sequence_length,List.map_append,List.sum_append]
    omega
  have oldPayload : (Encoding.sequence Encoding.node state.1.toList).length ≤
      ((Encoding.array Encoding.node).encode state.1).length := by
    simp only [Encoding.array,Encoding.transport,Encoding.list,List.length_append]
    omega
  have nextSize : (visited.foldl commitRecord state).1.size ≤ width := by dsimp [width];omega
  have nextBits : (visited.foldl commitRecord state).1.size.size ≤ K :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans (nextSize.trans widthBound)
  have payloadBound : (Encoding.sequence Encoding.node (visited.foldl commitRecord state).1.toList).length ≤ K := by
    dsimp [K,commitInputSize]
    omega
  have mapInitial : ((Encoding.array Encoding.natural).encode state.2).length ≤ K := by
    dsimp [K,commitInputSize];omega
  have multiply := Nat.mul_le_mul (countVisited.trans (recordCount.trans (show
      ((Encoding.list Sort.recordCodec).encode records).length ≤ K by dsimp [K,commitInputSize];omega)))
    (show 2*width+1 ≤ 3*K by omega)
  dsimp only
  constructor
  · simp only [Encoding.array,Encoding.transport,Encoding.list,List.length_append,Array.length_toList,Encoding.natural_length]
    change _ ≤ 10*K^2
    omega
  · change _ ≤ 10*K^2
    nlinarith only [mapping,mapInitial,multiply,linear]

end Counting.StackMachine.DagUpdate.Canonical
