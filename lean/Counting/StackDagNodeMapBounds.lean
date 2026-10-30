import Counting.StackDagNodeMap
import Counting.DagReferenceEncodingBounds

namespace Counting.StackMachine.DagUpdate.NodeMap
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

theorem node_fields_length (node : Executable.Node) :
    node.level.bits.length+(parentNumber node).bits.length+node.degree.bits.length+
      ((Encoding.list edgeCodec).encode node.incoming).length ≤ (Encoding.node.encode node).length := by
  simp only [Encoding.node,Encoding.transport,Encoding.nodeFields,Encoding.product,
    Encoding.optionalNatural,Encoding.boolean,parentNumber,edgeCodec,List.length_append,
    Encoding.natural_length,Encoding.bits_length,List.length_cons,List.length_nil]
  omega

theorem referenceMapBudget_polynomial (mapping : Array Nat) (node : Executable.Node)
    (suffix : List Bool) :
    referenceMapBudget mapping node suffix ≤
      30000000000*((Encoding.node.encode node).length+suffix.length+
        ((Encoding.array Encoding.natural).encode mapping).length+1)^7 := by
  let A := (Encoding.node.encode node).length
  let M := ((Encoding.array Encoding.natural).encode mapping).length
  let K := A+suffix.length+M+1
  let target := Executable.referenceMap mapping node
  have fields := node_fields_length node
  have targetFields := node_fields_length target
  have positive : 1 ≤ K := by omega
  have labelBound : node.level.bits.length+(parentNumber node).bits.length+node.degree.bits.length ≤ K := by
    change _ ≤ A at fields
    omega
  have parentBound : M+(parentNumber node).size+1 ≤ K := by
    rw [←Encoding.bits_length]
    change _ ≤ A at fields
    omega
  have incomingBound : ((Encoding.list edgeCodec).encode node.incoming).length+suffix.length+M+2 ≤ 2*K := by
    change _ ≤ A at fields
    omega
  have outputBound : (Encoding.node.encode target).length ≤ 5*K^2 := by
    have output := Executable.referenceMap_encoded_polynomial mapping node
    have base : A+M+1 ≤ K := by omega
    exact output.trans (Nat.mul_le_mul_left 5 (Nat.pow_le_pow_left base 2))
  have targetLabelBound : target.level.bits.length+(parentNumber target).bits.length+target.degree.bits.length ≤ 5*K^2 := by
    omega
  have targetIncomingBound : ((Encoding.list edgeCodec).encode target.incoming).length ≤ 5*K^2 := by
    omega
  have oldParentBound : (parentNumber node).bits.length ≤ K := by omega
  have p3 := Nat.pow_le_pow_left parentBound 3
  have p7 := Nat.pow_le_pow_left incomingBound 7
  have one : 1 ≤ K^7 := one_le_pow₀ positive
  have k1 : K ≤ K^7 := by simpa only [pow_one] using (pow_le_pow_right₀ positive (show 1 ≤ 7 by decide))
  have k2 : K^2 ≤ K^7 := pow_le_pow_right₀ positive (by decide)
  have k3 : K^3 ≤ K^7 := pow_le_pow_right₀ positive (by decide)
  change referenceMapBudget mapping node suffix ≤ 30000000000*K^7
  dsimp only [referenceMapBudget]
  change 5*(node.level.bits.length+(parentNumber node).bits.length+node.degree.bits.length)+11+
    2100*(M+(parentNumber node).size+1)^3+
    (200000000*(((Encoding.list edgeCodec).encode node.incoming).length+suffix.length+M+2)^7+2)+
    (9*(target.level.bits.length+(parentNumber target).bits.length+target.degree.bits.length)+
      2*((Encoding.list edgeCodec).encode target.incoming).length+
      2*(Encoding.node.encode target).length+(parentNumber node).bits.length+35)+3 ≤ _
  rw [mul_pow] at p7
  norm_num only [Nat.reducePow] at p7
  nlinarith only [labelBound,p3,p7,targetLabelBound,targetIncomingBound,outputBound,
    oldParentBound,one,k1,k2,k3]

/-- A canonical node and mapping suffice. No validity, sortedness, positive
count or in-range-reference premise is needed for this exact transduction. -/
theorem referenceMap_executes_polynomial (store : Store 62) (mapping : Array Nat)
    (node : Executable.Node) (suffix : List Bool)
    (input : store 0=Encoding.node.encode node++suffix)
    (mapInput : store 1=(Encoding.array Encoding.natural).encode mapping)
    (empty : ∀ r : Fin 64,2 ≤ r.val → r.val ≤ 48 → store r=[]) :
    ∃ time ≤ 30000000000*((store 0).length+(store 1).length+1)^7,
      Executes referenceMap store time
        (Function.update (Function.update store 0 suffix) 3
          (Encoding.node.encode (Executable.referenceMap mapping node))) := by
  obtain ⟨time,bound,ran⟩ := referenceMap_executes store mapping node suffix input mapInput empty
  refine ⟨time,?_,ran⟩
  rw [input,mapInput,List.length_append]
  exact bound.trans (referenceMapBudget_polynomial mapping node suffix)

end Counting.StackMachine.DagUpdate.NodeMap
