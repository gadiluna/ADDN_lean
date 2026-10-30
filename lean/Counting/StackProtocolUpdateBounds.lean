import Counting.StackProtocolUpdatePrepare
import Counting.DagRawValidity

namespace Counting.StackMachine.ProtocolUpdate
open Routine Executable
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

def rawWord (old : Vista) (messages : List (Vista×Nat)) (degree : Nat) : List Bool :=
  DagUpdate.Raw.inputWord (old.node old.bottom).level (old.node old.bottom).leader degree old messages

theorem rawWord_eq (old : Vista) (messages : List (Vista×Nat)) (degree : Nat) :
    rawWord old messages degree=ProtocolBottom.outputWord old++Encoding.natural.encode degree++
      Encoding.vista.encode old++(Encoding.list DagUpdate.Receive.messageCodec).encode messages := by
  simp only [rawWord,DagUpdate.Raw.inputWord,DagUpdate.Raw.inputCodec,Encoding.product,
    ProtocolBottom.outputWord,Encoding.boolean,List.append_assoc]

theorem rawWord_length (old : Vista) (messages : List (Vista×Nat)) (degree : Nat) (valid : old.valid=true) :
    (rawWord old messages degree).length+1≤4*((inputWord old messages degree).length+1) := by
  have nodeBound:=Encoding.nodeBits_le_vista old old.bottom (RealizabilityVerifier.bottom_inside old valid)
  have bottomBound:(ProtocolBottom.outputWord old).length≤3*((Encoding.vista.encode old).length+1) := by
    simp only [ProtocolBottom.outputWord,List.length_append,List.length_singleton,Encoding.natural_length]
    unfold Encoding.nodeBits at nodeBound
    omega
  simp only [rawWord_eq,inputWord_eq,List.length_append,Encoding.frame_length] at *
  omega

/-- Interning the newly assembled node increases the encoded pool only
quadratically in the complete encoded receiver input. -/
theorem updated_encoding_length (round : Nat) (leader : Bool) (degree : Nat) (old : Vista)
    (messages : List (Vista×Nat)) :
    (Encoding.vista.encode (DagUpdate.Raw.updated round leader degree old messages)).length≤
      110*((DagUpdate.Raw.inputWord round leader degree old messages).length+1)^2 := by
  let K:=(DagUpdate.Raw.inputWord round leader degree old messages).length+1
  let pool:=(messages.foldl mergeMessage (old.nodes,[])).1
  let node:=DagUpdate.Raw.newNode round old.bottom leader degree (messages.foldl mergeMessage (old.nodes,[])).2
  let result:=intern pool node
  have poolBound:= (DagUpdate.Raw.merged_encoded_bound round leader degree old messages).1
  have nodeBound:= DagUpdate.Raw.newNode_encoded_bound round leader degree old messages
  change ((Encoding.array Encoding.node).encode pool).length≤20*K^2 at poolBound
  change (Encoding.node.encode node).length≤40*K^2 at nodeBound
  have nodesBound:=DagUpdate.Raw.intern_encoded_length pool node
  have indexBound:result.2.size≤((Encoding.array Encoding.node).encode pool).length+1 := by
    have index:=intern_index_lt pool node
    have capacity:=intern_size_le_succ pool node
    have count:=Encoding.array_size_le_length Encoding.node pool (fun node _=>Encoding.node_positive_length node)
    have bits:result.2.size≤result.2:=Nat.size_le.mpr Nat.lt_two_pow_self
    change result.2<(intern pool node).1.size at index
    omega
  have positive:1≤K^2 := by dsimp [K];exact Nat.one_le_pow' _ _
  change (Encoding.vista.encode (⟨result.1,result.2⟩:Vista)).length≤110*K^2
  simp only [Encoding.vista,Encoding.transport,Encoding.product,List.length_append,Encoding.natural_length]
  change ((Encoding.array Encoding.node).encode result.1).length+ (2*result.2.size+1)≤110*K^2
  change ((Encoding.array Encoding.node).encode result.1).length≤
    ((Encoding.array Encoding.node).encode pool).length+(Encoding.node.encode node).length+2 at nodesBound
  omega

theorem rawUpdate_encoding_length (old : Vista) (messages : List (Vista×Nat)) (degree : Nat)
    (valid : old.valid=true)
    (received : ∀m∈messages,m.1.valid=true ∧ (m.1.node m.1.bottom).level=(old.node old.bottom).level) :
    (Encoding.vista.encode (rawUpdate old messages degree)).length≤
      1760*((inputWord old messages degree).length+1)^2 := by
  have bound:=updated_encoding_length (old.node old.bottom).level (old.node old.bottom).leader degree old messages
  rw [DagUpdate.Raw.updated_eq_rawUpdate _ _ _ _ _ valid rfl rfl received] at bound
  have squared:=Nat.pow_le_pow_left (rawWord_length old messages degree valid) 2
  have scaled:=Nat.mul_le_mul_left 110 squared
  rw [Nat.mul_pow] at scaled
  change _≤110*(4^2*((inputWord old messages degree).length+1)^2) at scaled
  rw [←Nat.mul_assoc,show 110*4^2=1760 by norm_num] at scaled
  exact bound.trans scaled

end Counting.StackMachine.ProtocolUpdate
