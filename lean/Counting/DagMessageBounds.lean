import Counting.DagImportPrefixBounds
import Counting.DagSemanticsUpdate

namespace Counting.Executable

def messageEncoding : Encoding.Codec (Vista×Nat) := Encoding.product Encoding.vista Encoding.natural

def messageNodes (messages : List (Vista×Nat)) : Nat :=
  (messages.map (fun m=>m.1.nodes.size)).sum

theorem message_fields_length (message : Vista×Nat) :
    ((Encoding.array Encoding.node).encode message.1.nodes).length ≤
      (messageEncoding.encode message).length := by
  simp only [messageEncoding,Encoding.product,Encoding.vista,Encoding.transport,
    Encoding.array,List.length_append]
  omega

theorem message_count_bits (message : Vista×Nat) :
    message.2.size ≤ (messageEncoding.encode message).length := by
  simp only [messageEncoding,Encoding.product,List.length_append,Encoding.natural_length]
  omega

theorem message_node_count (message : Vista×Nat) :
    message.1.nodes.size ≤ (messageEncoding.encode message).length :=
  (Encoding.array_size_le_length Encoding.node message.1.nodes
    (fun node _=>Encoding.node_positive_length node)).trans (message_fields_length message)

theorem messageNodes_length (messages : List (Vista×Nat)) :
    messageNodes messages ≤ (Encoding.sequence messageEncoding messages).length := by
  induction messages with
  | nil => simp [messageNodes,Encoding.sequence]
  | cons message messages ih =>
    have head := message_node_count message
    simpa only [messageNodes,List.map_cons,List.sum_cons,Encoding.sequence,List.length_append]
      using Nat.add_le_add head ih

theorem message_count_length (messages : List (Vista×Nat)) :
    messages.length ≤ (Encoding.sequence messageEncoding messages).length := by
  induction messages with
  | nil => simp [Encoding.sequence]
  | cons message messages ih =>
    have positive : 1 ≤ (messageEncoding.encode message).length := by
      simp only [messageEncoding,Encoding.product,List.length_append,Encoding.natural_length]
      omega
    simp only [Encoding.sequence,List.length_append,List.length_cons]
    omega

theorem mergeMessages_size_le (state : MergeState) (messages : List (Vista×Nat)) :
    (messages.foldl mergeMessage state).1.size ≤ state.1.size+messageNodes messages := by
  induction messages generalizing state with
  | nil => simp [messageNodes]
  | cons message messages ih =>
    have next := importVista_size_le state.1 message.1
    have rest := ih (mergeMessage state message)
    simp only [List.foldl_cons,messageNodes,List.map_cons,List.sum_cons]
    change (messages.foldl mergeMessage (mergeMessage state message)).1.size ≤
      (importVista state.1 message.1).1.size+messageNodes messages at rest
    simp only [messageNodes] at rest
    omega

/-- Imported node encodings grow additively across received messages.
This uniform width bound avoids iterating a polynomial size estimate and
mistaking that recurrence for a polynomial bound on the whole update. -/
theorem mergeMessages_payload_bound (state : MergeState) (messages : List (Vista×Nat))
    (width : Nat) (capacity : state.1.size+messageNodes messages ≤ width) :
    (Encoding.sequence Encoding.node (messages.foldl mergeMessage state).1.toList).length ≤
      (Encoding.sequence Encoding.node state.1.toList).length+
        (4*width+6)*(Encoding.sequence messageEncoding messages).length ∧
    (Encoding.sequence (Encoding.product Encoding.natural Encoding.natural)
      (messages.foldl mergeMessage state).2).length ≤
      (Encoding.sequence (Encoding.product Encoding.natural Encoding.natural) state.2).length+
        messages.length*(2*width+2)+2*(Encoding.sequence messageEncoding messages).length := by
  induction messages generalizing state with
  | nil => simp [Encoding.sequence]
  | cons message messages ih =>
    let imported := importVista state.1 message.1
    have importEq : imported=message.1.nodes.toList.foldl importStep (state.1,#[]) := by
      simp only [imported,importVista,←Array.foldl_toList]
      rfl
    have capacityHead : state.1.size+message.1.nodes.size ≤ width := by
      simp only [messageNodes,List.map_cons,List.sum_cons] at capacity
      omega
    have payload := importFold_payload_bound message.1.nodes.toList (state.1,#[]) width
      (by simpa using capacityHead) (by simp)
    rw [←importEq] at payload
    have nextSize := importVista_size_le state.1 message.1
    have capacityNext : (mergeMessage state message).1.size+messageNodes messages ≤ width := by
      change imported.1.size+messageNodes messages ≤ width
      simp only [messageNodes,List.map_cons,List.sum_cons] at capacity
      dsimp only [imported,messageNodes]
      omega
    obtain ⟨poolTail,edgeTail⟩ := ih (mergeMessage state message) capacityNext
    have bits := message_fields_length message
    have count := message_node_count message
    have nodeBits : (Encoding.sequence Encoding.node message.1.nodes.toList).length ≤
        (messageEncoding.encode message).length := by
      simp only [Encoding.array,Encoding.transport,Encoding.list,List.length_append] at bits
      omega
    have body : (Encoding.sequence Encoding.node message.1.nodes.toList).length+
        message.1.nodes.toList.length ≤ 2*(messageEncoding.encode message).length := by
      simp only [Array.length_toList]
      omega
    have scale := Nat.mul_le_mul_left (2*width+3) body
    have reference : (imported.2[message.1.bottom]?.getD 0).size ≤ width :=
      (Nat.size_le.mpr Nat.lt_two_pow_self).trans (payload.2 message.1.bottom)
    have add := addCount_encoded_length (imported.2[message.1.bottom]?.getD 0) message.2 state.2
    have amount := message_count_bits message
    change (Encoding.sequence Encoding.node (messages.foldl mergeMessage
      (mergeMessage state message)).1.toList).length ≤
      (Encoding.sequence Encoding.node imported.1.toList).length+
        (4*width+6)*(Encoding.sequence messageEncoding messages).length at poolTail
    change (Encoding.sequence (Encoding.product Encoding.natural Encoding.natural)
      (messages.foldl mergeMessage (mergeMessage state message)).2).length ≤
      (Encoding.sequence (Encoding.product Encoding.natural Encoding.natural)
        (addCount (imported.2[message.1.bottom]?.getD 0) message.2 state.2)).length+
      messages.length*(2*width+2)+2*(Encoding.sequence messageEncoding messages).length at edgeTail
    simp only [List.foldl_cons,Encoding.sequence,List.length_append,List.length_cons]
    constructor
    · nlinarith only [poolTail,payload.1,scale]
    · nlinarith only [edgeTail,add,reference,amount]

end Counting.Executable
