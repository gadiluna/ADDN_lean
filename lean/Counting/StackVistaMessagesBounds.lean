import Counting.StackVistaMessagesComplete
import Counting.StackVistaMessageBounds

namespace Counting.StackMachine.DagUpdate.Receive
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def messagesBase (state : Executable.MergeState) (messages : List (Executable.Vista×Nat))
    (suffix : List Bool) : Nat :=
  ((Encoding.array Encoding.node).encode state.1).length+
    ((Encoding.list edgeCodec).encode state.2).length+
    (Encoding.sequence messageCodec messages).length+suffix.length+1

theorem messageStepBudget_prefix (initial : Executable.MergeState)
    (messages visited remaining : List (Executable.Vista×Nat)) (message : Executable.Vista×Nat)
    (suffix : List Bool) (partition : visited++message::remaining=messages) :
    let state := visited.foldl Executable.mergeMessage initial
    messageStepBudget state.1 message state.2
      (Encoding.sequence messageCodec (message::remaining)++suffix).length ≤
      messageStepCoefficient*10000^15*(messagesBase initial messages suffix)^60 := by
  let state := visited.foldl Executable.mergeMessage initial
  let K := messagesBase initial messages suffix
  let cap := 10000*K^4
  have positive : 1≤K := by dsimp only [K,messagesBase];omega
  have square : K≤K^2 := Nat.le_self_pow (by decide) _
  have fourth : K^2≤K^4 := Nat.pow_le_pow_right positive (by decide)
  have one : 1≤K^4 := one_le_pow₀ positive
  have capPositive : 1≤cap := by dsimp only [cap];omega
  have originalBase : ((Encoding.array Encoding.node).encode initial.1).length+
      ((Encoding.list (Encoding.product Encoding.natural Encoding.natural)).encode initial.2).length+
      (Encoding.sequence Executable.messageEncoding messages).length+1 ≤ K := by
    dsimp only [K,messagesBase,edgeCodec,messageCodec,Executable.messageEncoding]
    omega
  have prefixBound := Executable.mergeMessages_prefix_encoded_polynomial initial visited messages
    ⟨message::remaining,partition⟩
  dsimp only at prefixBound
  have squareBound := Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left originalBase 2)
  have poolBound : ((Encoding.array Encoding.node).encode state.1).length≤20*K^2 :=
    prefixBound.1.trans squareBound
  have edgeBound : ((Encoding.list edgeCodec).encode state.2).length≤20*K^2 :=
    prefixBound.2.trans squareBound
  have following := Executable.mergeMessages_prefix_encoded_polynomial initial (visited++[message]) messages
    ⟨remaining,by simpa only [List.append_assoc,List.singleton_append] using partition⟩
  dsimp only at following
  have nextEq : (visited++[message]).foldl Executable.mergeMessage initial=
      Executable.mergeMessage state message := by
    simp only [List.foldl_append,List.foldl_cons,List.foldl_nil,state]
  rw [nextEq] at following
  have nextEdge : ((Encoding.list edgeCodec).encode (Executable.mergeMessage state message).2).length≤20*K^2 :=
    following.2.trans squareBound
  have sourceBound : (Encoding.sequence messageCodec (message::remaining)++suffix).length≤K := by
    have full : (Encoding.sequence messageCodec messages).length=
        (Encoding.sequence messageCodec visited).length+
          (Encoding.sequence messageCodec (message::remaining)).length := by
      rw [←partition]
      simp only [Encoding.sequence_length,List.map_append,List.sum_append]
    dsimp only [K,messagesBase]
    rw [List.length_append]
    omega
  have messageBound : (messageCodec.encode message).length≤K := by
    simp only [Encoding.sequence,List.length_append] at sourceBound
    omega
  have nodeBound := (Executable.message_fields_length message).trans messageBound
  have imported := (Executable.importVista_encoded_polynomial state.1 message.1).2
  have mapBase : ((Encoding.array Encoding.node).encode state.1).length+
      ((Encoding.array Encoding.node).encode message.1.nodes).length+1≤22*K^2 := by omega
  have mappingBound : ((Encoding.array Encoding.natural).encode
      (Executable.importVista state.1 message.1).2).length≤cap := by
    have bounded := imported.trans (Nat.mul_le_mul_left 10 (Nat.pow_le_pow_left mapBase 2))
    change _ ≤ 10000*K^4
    nlinarith only [bounded,show (22*K^2)^2=484*K^4 by ring]
  have bounded := messageStepBudget_cap state message _ cap capPositive
    (poolBound.trans (by dsimp only [cap];omega))
    (messageBound.trans (by dsimp only [cap];omega))
    (sourceBound.trans (by dsimp only [cap];omega))
    (edgeBound.trans (by dsimp only [cap];omega)) mappingBound
    (nextEdge.trans (by dsimp only [cap];omega))
  calc
    _ ≤ messageStepCoefficient*cap^15 := bounded
    _ = messageStepCoefficient*10000^15*K^60 := by dsimp only [cap];ring

theorem messageLoopBudget_suffix_bound (initial : Executable.MergeState)
    (messages visited remaining : List (Executable.Vista×Nat)) (suffix : List Bool)
    (partition : visited++remaining=messages) :
    messageLoopBudget (visited.foldl Executable.mergeMessage initial) remaining suffix ≤
      remaining.length*(messageStepCoefficient*10000^15*(messagesBase initial messages suffix)^60+2)+1 := by
  induction remaining generalizing visited with
  | nil => simp [messageLoopBudget]
  | cons message remaining ih =>
    have first := messageStepBudget_prefix initial messages visited remaining message suffix partition
    have tail := ih (visited++[message])
      (by simpa only [List.append_assoc,List.singleton_append] using partition)
    have nextEq : (visited++[message]).foldl Executable.mergeMessage initial=
        Executable.mergeMessage (visited.foldl Executable.mergeMessage initial) message := by
      simp only [List.foldl_append,List.foldl_cons,List.foldl_nil]
    rw [nextEq] at tail
    dsimp only at first
    simp only [messageLoopBudget,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

def messageLoopCoefficient : Nat := messageStepCoefficient*10000^15+3

theorem messageLoopBudget_polynomial (state : Executable.MergeState)
    (messages : List (Executable.Vista×Nat)) (suffix : List Bool) :
    messageLoopBudget state messages suffix ≤
      messageLoopCoefficient*(messagesBase state messages suffix)^61 := by
  have full := messageLoopBudget_suffix_bound state messages [] messages suffix rfl
  simp only [List.foldl_nil] at full
  let K := messagesBase state messages suffix
  have count : messages.length≤K := by
    have bounded := Executable.message_count_length messages
    dsimp only [K,messagesBase,messageCodec,Executable.messageEncoding] at *
    omega
  have positive : 1≤K := by dsimp only [K,messagesBase];omega
  have scaled := Nat.mul_le_mul_right (messageStepCoefficient*10000^15*K^60+2) count
  have linear : K≤K^61 := Nat.le_self_pow (by decide) _
  have one : 1≤K^61 := one_le_pow₀ positive
  change _ ≤ messageLoopCoefficient*K^61
  change messageLoopBudget state messages suffix ≤ messages.length*
    (messageStepCoefficient*10000^15*K^60+2)+1 at full
  dsimp only [messageLoopCoefficient]
  nlinarith only [full,scaled,linear,one,show K*K^60=K^61 by ring]

end Counting.StackMachine.DagUpdate.Receive
