import Counting.StackDagReindexIncoming
import Counting.StackDagReindexUniform
import Counting.DagReindexPrefixBounds

namespace Counting.StackMachine.DagUpdate.Reindex
open Routine
set_option backward.isDefEq.respectTransparency false

theorem loopBudget_polynomial (mapping : List Nat) (source accumulator : List (Nat×Nat)) :
    loopBudget mapping source accumulator ≤ 100000000*
      (((Encoding.list Encoding.natural).encode mapping).length+
        (Encoding.sequence edgeCodec source).length+(Encoding.sequence edgeCodec accumulator).length+1)^7 := by
  let M:=((Encoding.list Encoding.natural).encode mapping).length
  let B:=(Encoding.sequence edgeCodec source).length
  let A:=(Encoding.sequence edgeCodec accumulator).length
  let S:=M+B+A+1
  have positive : 1 ≤ S := by omega
  have mappedBound (index : Nat) : (mapping[index]?.getD 0).bits.length ≤ M := by
    simpa [M,Encoding.bits_length,Encoding.array,Encoding.transport] using
      Encoding.naturalArray_entry_size_le mapping.toArray index
  have prefixBound (visited : List (Nat×Nat)) (before : visited.IsPrefix source) :
      ((Encoding.list edgeCodec).encode (visited.foldl (remap mapping) accumulator)).length ≤ 5*S^2 := by
    change ((Encoding.list edgeCodec).encode (visited.foldl (fun acc edge=>
      Executable.addCount (mapping[edge.1]?.getD 0) edge.2 acc) accumulator)).length ≤ 5*S^2
    simpa [S,M,B,A,Encoding.array,Encoding.transport,edgeCodec] using
      Executable.reindexPrefix_encoded_polynomial mapping.toArray visited source accumulator before
  have uniform:=loopBudget_uniform mapping source accumulator M B (5*S^2) (by rfl) mappedBound
    (fun edge member=>edge_bits_le_sequence source edge member) prefixBound
  have countBound : source.length ≤ S := by
    have count:=Executable.incoming_length_le_bits source
    change source.length ≤ B at count
    omega
  let K:=5*S^2+M+2*B+2
  have small : M+2*B+2 ≤ 3*S+2 := by dsimp only [S];omega
  have kernel : K ≤ 10*S^2 := by dsimp only [K];nlinarith only [positive,small]
  have power:=Nat.pow_le_pow_left kernel 3
  simp only [mul_pow] at power
  norm_num at power
  change loopBudget mapping source accumulator ≤ source.length*(20000*K^3+2)+1 at uniform
  have growth:=Nat.mul_le_mul countBound (Nat.add_le_add_right (Nat.mul_le_mul_left 20000 power) 2)
  have linear : S ≤ S^7 := Nat.le_self_pow (by decide) S
  change _ ≤ 100000000*S^7
  nlinarith only [uniform,growth,linear,positive]

theorem incoming_executes_polynomial (store : Store 38) (mapping : List Nat) (source accumulator : List (Nat×Nat))
    (suffix : List Bool)
    (input : store 0=(Encoding.list edgeCodec).encode source++suffix)
    (mapInput : store 1=(Encoding.list Encoding.natural).encode mapping)
    (current : store 2=(Encoding.list edgeCodec).encode accumulator)
    (empty : ∀ r : Fin 40,3 ≤ r.val → r.val ≤ 37 → store r=[]) :
    ∃ time ≤ 200000000*((store 0).length+(store 1).length+(store 2).length+1)^7,
      Executes incoming store time (Function.update (Function.update store 0 suffix) 2
        ((Encoding.list edgeCodec).encode (source.foldl (remap mapping) accumulator))) := by
  obtain ⟨time,bound,ran⟩:=incoming_executes store mapping source accumulator suffix input mapInput current empty
  have sourceBits : (Encoding.sequence edgeCodec source).length ≤ (store 0).length := by
    rw [input];simp only [Encoding.list,List.length_append];omega
  have currentBits : (Encoding.sequence edgeCodec accumulator).length ≤ (store 2).length := by
    rw [current];simp only [Encoding.list,List.length_append];omega
  let T:=(store 0).length+(store 1).length+(store 2).length+1
  have positive : 1 ≤ T := by omega
  have poly:=loopBudget_polynomial mapping source accumulator
  have inputBound : ((Encoding.list Encoding.natural).encode mapping).length+
      (Encoding.sequence edgeCodec source).length+(Encoding.sequence edgeCodec accumulator).length+1 ≤ T := by
    rw [←mapInput];omega
  have loopBound:=poly.trans (Nat.mul_le_mul_left 100000000 (Nat.pow_le_pow_left inputBound 7))
  have headerBase : (store 0).length+1 ≤ T := by omega
  have headerDegree : T^3 ≤ T^7 := Nat.pow_le_pow_right positive (by decide)
  have headerBound:=(Nat.pow_le_pow_left headerBase 3).trans headerDegree
  have unit : 1 ≤ T^7 := one_le_pow₀ positive
  refine ⟨time,?_,ran⟩
  change time ≤ 200000000*T^7
  nlinarith only [bound,loopBound,headerBound,unit]

end Counting.StackMachine.DagUpdate.Reindex
