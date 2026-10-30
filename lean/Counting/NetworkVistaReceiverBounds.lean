import Counting.NetworkVistaCollectActual
import Counting.NetworkVistaBundleBounds

namespace Counting.StackMachine.NetworkVista.Receiver
open Encoding

theorem sum_size_le_sequence (values : List Nat) :
    values.sum.size≤(Encoding.sequence Encoding.natural values).length := by
  apply Nat.size_le.mpr
  induction values with
  | nil => simp [Encoding.sequence]
  | cons head tail ih =>
    have h := Nat.lt_size_self head
    have p : 1≤2^head.size := Nat.one_le_pow _ _ (by decide)
    have q : 1≤2^(Encoding.sequence Encoding.natural tail).length := Nat.one_le_pow _ _ (by decide)
    have sumBound : head+tail.sum<2^(head.size+(Encoding.sequence Encoding.natural tail).length+1) := by
      simp only [pow_add,pow_one]
      nlinarith
    have exponent : head.size+(Encoding.sequence Encoding.natural tail).length+1≤
        2*head.size+1+(Encoding.sequence Encoding.natural tail).length := by omega
    have bigger := Nat.pow_le_pow_right (by decide : 1≤2) exponent
    simp only [List.sum_cons,Encoding.sequence,List.length_append,Encoding.natural_length]
    exact sumBound.trans_le bigger

theorem row_sum_bits_le (row : Array Nat) :
    row.toList.sum.bits.length≤((Encoding.array Encoding.natural).encode row).length := by
  rw [Encoding.bits_length]
  apply (sum_size_le_sequence row.toList).trans
  simp only [Encoding.array,Encoding.transport,Encoding.list,List.length_append]
  omega

theorem messages_length_bound (n : Nat) (graph : Simulation.RoundGraph) (views : Fin n→Executable.Vista)
    (receiver : Fin n) (shape : Encoding.matrixShape n graph=true) :
    ((Encoding.list (Encoding.product Encoding.vista Encoding.natural)).encode
      (Executable.senderBundles (List.finRange n) (Encoding.matrixEdge graph n) views receiver)).length≤
      2*n+1+((Encoding.array Encoding.vista).encode (Array.ofFn views)).length+
        ((Encoding.array (Encoding.array Encoding.natural)).encode graph).length := by
  have graphSize : graph.size=n := by
    simp only [Encoding.matrixShape,Bool.and_eq_true,beq_iff_eq] at shape
    exact shape.1
  let pairs := physicalSenderPairs n graph views
  let messages := receivedPairs receiver.val pairs
  have same : messages=Executable.senderBundles (List.finRange n) (Encoding.matrixEdge graph n) views receiver := by
    exact receivedPairs_allAgents n graph views receiver
  have count := receivedPairs_length_le receiver.val pairs
  have code := receivedPairs_code_length_le receiver.val pairs
  rw [physicalSenderPairs_length] at count
  rw [physicalSenderPairs_views,physicalSenderPairs_rows n graph views graphSize] at code
  have size : messages.length.size≤n :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans count
  rw [←same]
  change (Encoding.natural.encode messages.length++Encoding.sequence (Encoding.product Encoding.vista Encoding.natural) messages).length≤
    2*n+1+(Encoding.natural.encode (Array.ofFn views).toList.length++Encoding.sequence Encoding.vista (Array.ofFn views).toList).length+
      (Encoding.natural.encode graph.toList.length++Encoding.sequence (Encoding.array Encoding.natural) graph.toList).length
  change (Encoding.sequence (Encoding.product Encoding.vista Encoding.natural) messages).length≤_ at code
  simp only [List.length_append,Encoding.natural_length]
  omega

end Counting.StackMachine.NetworkVista.Receiver
