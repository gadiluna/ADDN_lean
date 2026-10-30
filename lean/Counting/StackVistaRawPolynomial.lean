import Counting.StackVistaRawComplete
import Counting.StackVistaRawBounds

namespace Counting.StackMachine.DagUpdate.Raw
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

def completeCoefficient : Nat :=
  Receive.messageLoopCoefficient+DagParser.nodes.coefficient+8000*61^4+5000

/-- Uniform runtime for every typed input, including invalid DAG fields,
zero bundles and arbitrary binary labels. Correct physical semantics is a
separate theorem with the input model's validity premises. -/
theorem completeBudget_polynomial (round : Nat) (leader : Bool) (degree : Nat)
    (old : Executable.Vista) (messages : List (Executable.Vista×Nat)) :
    completeBudget round leader degree old messages ≤
      completeCoefficient*((inputWord round leader degree old messages).length+1)^61 := by
  let K := (inputWord round leader degree old messages).length+1
  let merged := messages.foldl Executable.mergeMessage (old.nodes,[])
  let node := newNode round old.bottom leader degree merged.2
  have positive : 1 ≤ K := by dsimp [K]; omega
  have base := input_messagesBase round leader degree old messages
  have loopLimit := (Receive.messageLoopBudget_polynomial (old.nodes,[]) messages []).trans
    (Nat.mul_le_mul_left Receive.messageLoopCoefficient (Nat.pow_le_pow_left base 61))
  have poolLimit := (merged_encoded_bound round leader degree old messages).1
  have nodeLimit := newNode_encoded_bound round leader degree old messages
  have finishLimit := finishBudget_cap merged.1 node K positive poolLimit nodeLimit
  have assembleLimit := assembleBudget_polynomial round leader degree old messages
  have prepareLimit := prepareBudget_polynomial round leader degree old messages
  have length := inputWord_length round leader degree old messages
  have headerBase : ((Encoding.list Receive.messageCodec).encode messages).length+1 ≤ K := by
    dsimp [K]; omega
  have headerLimit := Nat.mul_le_mul_left 1820 (Nat.pow_le_pow_left headerBase 3)
  have second : K^2 ≤ K^61 := Nat.pow_le_pow_right positive (by decide)
  have third : K^3 ≤ K^61 := Nat.pow_le_pow_right positive (by decide)
  have fourth : K^4 ≤ K^61 := Nat.pow_le_pow_right positive (by decide)
  have eighth : K^8 ≤ K^61 := Nat.pow_le_pow_right positive (by decide)
  have one : 1 ≤ K^61 := one_le_pow₀ positive
  have preparing := prepareLimit.trans (Nat.mul_le_mul_left (DagParser.nodes.coefficient+100) fourth)
  have assembling := assembleLimit.trans (Nat.mul_le_mul_left 300 second)
  have finishing := finishLimit.trans (Nat.mul_le_mul_left finishCoefficient eighth)
  have header := headerLimit.trans (Nat.mul_le_mul_left 1820 third)
  change _ ≤ completeCoefficient*K^61
  unfold completeBudget
  change prepareBudget round degree old messages+
    1820*(((Encoding.list Receive.messageCodec).encode messages).length+1)^3+
    Receive.messageLoopBudget (old.nodes,[]) messages []+
    assembleBudget round old.bottom leader degree merged.2+finishBudget merged.1 node+4 ≤ _
  change Receive.messageLoopBudget (old.nodes,[]) messages [] ≤ Receive.messageLoopCoefficient*K^61 at loopLimit
  unfold completeCoefficient finishCoefficient at *
  nlinarith only [preparing,assembling,finishing,header,loopLimit,one]

theorem complete_polynomial (round : Nat) (leader : Bool) (degree : Nat)
    (old : Executable.Vista) (messages : List (Executable.Vista×Nat)) :
    ∃ time ≤ completeCoefficient*((inputWord round leader degree old messages).length+1)^61,
      Executes complete (inputStore 94 (inputWord round leader degree old messages)) time
        (outputStore 94 (Encoding.vista.encode (updated round leader degree old messages))) := by
  obtain ⟨time,bound,run⟩ := complete_executes round leader degree old messages
  exact ⟨time,bound.trans (completeBudget_polynomial round leader degree old messages),run⟩

end Counting.StackMachine.DagUpdate.Raw
