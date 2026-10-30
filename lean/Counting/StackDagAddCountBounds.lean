import Counting.StackDagAddCount
import Counting.DagUpdateEncodingBounds

namespace Counting.StackMachine.DagUpdate
open Routine
set_option backward.isDefEq.respectTransparency false

/-- Every sparse entry is charged to its actual serialized occurrence. -/
theorem edge_bits_le_sequence (edges : List (Nat×Nat)) (edge : Nat×Nat) (member : edge∈edges) :
    edge.1.bits.length+edge.2.bits.length ≤ (Encoding.sequence edgeCodec edges).length := by
  induction edges with
  | nil=>simp at member
  | cons head rest ih=>
    simp only [List.mem_cons] at member
    rcases member with equal|member
    · subst edge
      simp only [Encoding.sequence,edgeCodec,Encoding.product,List.length_append,
        Encoding.natural_length,Encoding.bits_length]
      omega
    · have previous:=ih member
      simp only [Encoding.sequence,List.length_append]
      omega

theorem addCountBudget_polynomial (index count : Nat) (edges : List (Nat×Nat)) (sourceLength : Nat)
    (encoded : (Encoding.sequence edgeCodec edges).length ≤ sourceLength) :
    addCountBudget index count edges sourceLength sourceLength ≤
      10000*(sourceLength+index.bits.length+count.bits.length+1)^3 := by
  let K:=sourceLength+index.bits.length+count.bits.length+1
  have positive : 1 ≤ K := by omega
  have sourceBound : sourceLength ≤ K := by omega
  have headerBound : sourceLength+1 ≤ K := by omega
  have entries:=Executable.incoming_length_le_bits edges
  change edges.length ≤ (Encoding.sequence edgeCodec edges).length at entries
  have outputLength:=Executable.addCount_length_le index count edges
  have outputBits:=Executable.addCount_encoded_length index count edges
  change (Encoding.sequence edgeCodec (Executable.addCount index count edges)).length ≤
    (Encoding.sequence edgeCodec edges).length+2*index.size+2*count.size+2 at outputBits
  rw [←Encoding.bits_length,←Encoding.bits_length] at outputBits
  have rowBound : edges.length ≤ K := by omega
  have stepBound : 110*(index.bits.length+count.bits.length+sourceLength)+162 ≤ 272*K := by omega
  have scanBound:=Nat.mul_le_mul rowBound stepBound
  have finishBound : (Encoding.sequence edgeCodec (Executable.addCount index count edges)).length+
      (Executable.addCount index count edges).length+1 ≤ 4*K := by omega
  have finishPower:=Nat.pow_le_pow_left finishBound 2
  have headerPower:=Nat.pow_le_pow_left headerBound 3
  have queryBound : index.bits.length+count.bits.length ≤ K := by omega
  have square : K ≤ K^2 := by nlinarith only [positive]
  have cube : K^2 ≤ K^3 := by nlinarith only [positive,show 0 ≤ K^2 by omega]
  dsimp only [addCountBudget]
  change _ ≤ 10000*K^3
  nlinarith only [scanBound,finishPower,headerPower,queryBound,square,cube,positive]

theorem addCount_executes_polynomial (extra : Nat) (w : AddWorkspace extra) (store : Store (extra+18))
    (index count : Nat) (edges : List (Nat×Nat)) (suffix : List Bool)
    (source : store (w 0)=(Encoding.list edgeCodec).encode edges++suffix)
    (query : store (w 1)=index.bits) (increment : store (w 2)=count.bits)
    (empty : ∀ j : Fin 20,j≠0 → j≠1 → j≠2 → store (w j)=[]) :
    ∃ time ≤ 10000*((store (w 0)).length+(store (w 1)).length+(store (w 2)).length+1)^3,
      Routine.Executes (addCount extra w) store time
        (Function.update (Function.update store (w 0) suffix) (w 3)
          ((Encoding.list edgeCodec).encode (Executable.addCount index count edges))) := by
  have streamBound : (Encoding.sequence edgeCodec edges).length ≤ (store (w 0)).length := by
    rw [source]
    simp only [Encoding.list,List.length_append]
    omega
  obtain ⟨time,bound,ran⟩:=addCount_executes extra w store index count edges suffix (store (w 0)).length
    source query increment empty (fun edge member=>(edge_bits_le_sequence edges edge member).trans streamBound)
  refine ⟨time,?_,ran⟩
  rw [query,increment]
  exact bound.trans (addCountBudget_polynomial index count edges (store (w 0)).length streamBound)

end Counting.StackMachine.DagUpdate
