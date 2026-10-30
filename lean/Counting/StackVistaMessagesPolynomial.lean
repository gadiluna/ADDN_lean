import Counting.StackVistaMessagesBounds

namespace Counting.StackMachine.DagUpdate.Receive
open Routine

def completeMessagesCoefficient : Nat := messageLoopCoefficient+3000

theorem completeMessagesBudget_polynomial (state : Executable.MergeState)
    (messages : List (Executable.Vista×Nat)) :
    completeMessagesBudget state messages ≤
      completeMessagesCoefficient*((messagesInput state messages).length+1)^61 := by
  let P := ((Encoding.array Encoding.node).encode state.1).length
  let E := ((Encoding.list edgeCodec).encode state.2).length
  let R := ((Encoding.list messageCodec).encode messages).length
  let K := (messagesInput state messages).length+1
  have inputLength : (messagesInput state messages).length=2*P+2*E+R+2 := by
    simp only [messagesInput,List.length_append,Encoding.frame_length,P,E,R]
    omega
  have positive : 1≤K := by dsimp only [K];omega
  have pBound : P≤K := by dsimp only [K];omega
  have eBound : E≤K := by dsimp only [K];omega
  have rBound : R≤K := by dsimp only [K];omega
  have sBound : (Encoding.sequence messageCodec messages).length≤R := by
    simp only [R,Encoding.list,List.length_append]
    omega
  have base : messagesBase state messages []≤K := by
    simp only [messagesBase,List.length_nil,Nat.add_zero]
    change P+E+(Encoding.sequence messageCodec messages).length+1≤K
    dsimp only [K]
    omega
  have loopLimit := (messageLoopBudget_polynomial state messages []).trans
    (Nat.mul_le_mul_left messageLoopCoefficient (Nat.pow_le_pow_left base 61))
  have outputs := Executable.mergeMessages_encoded_polynomial state messages
  have outputBase : ((Encoding.array Encoding.node).encode state.1).length+
      ((Encoding.list (Encoding.product Encoding.natural Encoding.natural)).encode state.2).length+
      (Encoding.sequence Executable.messageEncoding messages).length+1≤K := base
  dsimp only at outputs
  have poolLimit := outputs.1.trans (Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left outputBase 2))
  have edgesLimit := outputs.2.trans (Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left outputBase 2))
  change ((Encoding.list edgeCodec).encode (messages.foldl Executable.mergeMessage state).2).length ≤ 20*K^2 at edgesLimit
  have headerBase : R+1≤K := by dsimp only [K];omega
  have headerLimit := Nat.mul_le_mul_left 1820 (Nat.pow_le_pow_left headerBase 3)
  have square : K^2≤K^61 := Nat.pow_le_pow_right positive (by decide)
  have cubic : K^3≤K^61 := Nat.pow_le_pow_right positive (by decide)
  have linear : K≤K^61 := Nat.le_self_pow (by decide) _
  have one : 1≤K^61 := one_le_pow₀ positive
  change completeMessagesBudget state messages≤completeMessagesCoefficient*K^61
  change 5*P+5*E+6*R+1820*(R+1)^3+messageLoopBudget state messages []+
    6*((Encoding.array Encoding.node).encode (messages.foldl Executable.mergeMessage state).1).length+
    6*((Encoding.list edgeCodec).encode (messages.foldl Executable.mergeMessage state).2).length+27≤_
  dsimp only [completeMessagesCoefficient]
  nlinarith only [pBound,eBound,rBound,loopLimit,poolLimit,edgesLimit,headerLimit,square,cubic,linear,one]

theorem completeMessages_polynomial (state : Executable.MergeState)
    (messages : List (Executable.Vista×Nat)) :
    ∃ time ≤ completeMessagesCoefficient*((messagesInput state messages).length+1)^61,
      Executes completeMessages (inputStore 94 (messagesInput state messages)) time
        (outputStore 94 (messagesOutput state messages)) := by
  obtain ⟨time,bound,run⟩ := completeMessages_executes state messages
  exact ⟨time,bound.trans (completeMessagesBudget_polynomial state messages),run⟩

theorem completeMessages_halts (state : Executable.MergeState)
    (messages : List (Executable.Vista×Nat)) :
    ∃ time last,time≤completeMessagesCoefficient*((messagesInput state messages).length+1)^61 ∧
      HaltsAt completeMessages.program (messagesInput state messages) time last ∧
      last.store 1=messagesOutput state messages := by
  obtain ⟨time,bound,last,run,halt,stored⟩ := completeMessages_polynomial state messages
  exact ⟨time,last,bound,⟨run,halt⟩,by rw [stored];rfl⟩

end Counting.StackMachine.DagUpdate.Receive
