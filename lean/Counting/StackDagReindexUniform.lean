import Counting.StackDagReindexLoop

namespace Counting.StackMachine.DagUpdate.Reindex
set_option backward.isDefEq.respectTransparency false

def uniformBudget (M B W : Nat) : Nat := 20000*(W+M+2*B+2)^3

theorem stepBudget_uniform (mapping : List Nat) (edges : List (Nat×Nat)) (index count M B W : Nat)
    (mapBound : ((Encoding.list Encoding.natural).encode mapping).length ≤ M)
    (mappedBound : (mapping[index]?.getD 0).bits.length ≤ M)
    (edgeBound : index.bits.length+count.bits.length ≤ B)
    (currentBound : ((Encoding.list edgeCodec).encode edges).length ≤ W)
    (nextBound : ((Encoding.list edgeCodec).encode (remap mapping edges (index,count))).length ≤ W) :
    stepBudget mapping edges index count ≤ uniformBudget M B W := by
  let K:=W+M+2*B+2
  have positive : 1 ≤ K := by omega
  have queryLength : (Encoding.natural.encode index).length=2*index.bits.length+1 := by
    simp only [Encoding.natural_length,Encoding.bits_length]
  have readBase : ((Encoding.list Encoding.natural).encode mapping).length+
      (Encoding.natural.encode index).length+1 ≤ K := by omega
  have addBase : ((Encoding.list edgeCodec).encode edges).length+
      (mapping[index]?.getD 0).bits.length+count.bits.length+1 ≤ K := by omega
  have readPower:=Nat.pow_le_pow_left readBase 3
  have addPower:=Nat.pow_le_pow_left addBase 3
  have linear : 10*index.bits.length+6*count.bits.length+(Encoding.natural.encode index).length+
      (mapping[index]?.getD 0).bits.length+
      6*((Encoding.list edgeCodec).encode (Executable.addCount (mapping[index]?.getD 0) count edges)).length+24 ≤ 13*K := by
    change ((Encoding.list edgeCodec).encode (Executable.addCount (mapping[index]?.getD 0) count edges)).length ≤ W at nextBound
    omega
  have cube : K ≤ K^3 := Nat.le_self_pow (by decide) K
  change _ ≤ 20000*K^3
  dsimp only [stepBudget]
  nlinarith only [readPower,addPower,linear,cube]

theorem loopBudget_uniform (mapping : List Nat) (source accumulator : List (Nat×Nat)) (M B W : Nat)
    (mapBound : ((Encoding.list Encoding.natural).encode mapping).length ≤ M)
    (mappedBound : ∀ index : Nat,(mapping[index]?.getD 0).bits.length ≤ M)
    (edgeBound : ∀ edge∈source,edge.1.bits.length+edge.2.bits.length ≤ B)
    (prefixBound : ∀ visited : List (Nat×Nat),visited.IsPrefix source →
      ((Encoding.list edgeCodec).encode (visited.foldl (remap mapping) accumulator)).length ≤ W) :
    loopBudget mapping source accumulator ≤ source.length*(uniformBudget M B W+2)+1 := by
  induction source generalizing accumulator with
  | nil=>simp [loopBudget]
  | cons edge source ih=>
    have currentBound:=prefixBound [] (by simp)
    have nextBound:=prefixBound [edge] (by exact ⟨source,rfl⟩)
    have headBound:=stepBudget_uniform mapping accumulator edge.1 edge.2 M B W mapBound
      (mappedBound edge.1) (edgeBound edge (by simp)) currentBound nextBound
    have tailBound:=ih (remap mapping accumulator edge)
      (fun next member=>edgeBound next (by simp [member])) (by
        intro visited before
        obtain ⟨suffix,equal⟩:=before
        have extended : (edge::visited).IsPrefix (edge::source) := ⟨suffix,by simp [←equal]⟩
        exact prefixBound (edge::visited) extended)
    simp only [loopBudget,List.length_cons]
    nlinarith only [headBound,tailBound]

end Counting.StackMachine.DagUpdate.Reindex
