import Counting.StackAuditCompleteSpec

namespace Counting.StackMachine.AuditComplete

def witnessCodec : Encoding.Codec Executable.AuditWitness :=
  Encoding.transport (Encoding.product Encoding.natural (Encoding.array Encoding.natural))
    (fun witness=>(witness.anchor,witness.weights))
    (fun fields=>⟨fields.1,fields.2⟩) (by intro witness;rfl)

def answerCodec : Encoding.Codec (Option Executable.AuditWitness) := Encoding.optional witnessCodec

theorem witnessWord_eq_codec (answer : Option Executable.AuditWitness) :
    witnessWord answer=answerCodec.encode answer := by cases answer <;> rfl

theorem witnessWord_roundtrip (answer : Option Executable.AuditWitness) :
    answerCodec.decodeExact (witnessWord answer)=some answer := by
  apply (answerCodec.decodeExact_iff _ _).mpr
  exact (witnessWord_eq_codec answer).symm

theorem witnessWord_injective : Function.Injective witnessWord := by
  intro left right same
  rw [witnessWord_eq_codec,witnessWord_eq_codec] at same
  exact answerCodec.injective same

end Counting.StackMachine.AuditComplete
