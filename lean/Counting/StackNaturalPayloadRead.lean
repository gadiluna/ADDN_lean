import Counting.StackEncodingGuards

namespace Counting.StackMachine.EncodingPrograms
open Routine
set_option backward.isDefEq.respectTransparency false

def readNaturalPayload (extra : Nat) (source target temporary flag : Fin (extra+4)) : Routine (extra+2) :=
  sequence (ofProgram (flaggedProgram extra source target temporary flag))
    (ofProgram (combineFlagsProgram (extra+2) flag))

/-- On an already parsed canonical natural, retain its binary payload;
this never expands a numeric value into a unary counter. -/
theorem readNaturalPayload_executes (extra : Nat) (source target temporary flag : Fin (extra+4))
    (st : source≠target) (sw : source≠temporary) (tw : target≠temporary)
    (fs : flag≠source) (ft : flag≠target) (fw : flag≠temporary)
    (store : Fin (extra+4) → List Bool) (n : Nat) (suffix : List Bool)
    (accepted : Bool) (tail : List Bool)
    (input : store source=Encoding.natural.encode n++suffix)
    (status : store flag=accepted::tail) (scratch : store temporary=[]) (outEmpty : store target=[]) :
    ∃ time ≤ 3*(store source).length+8,
      Executes (readNaturalPayload extra source target temporary flag) store time
        (Function.update (Function.update store source suffix) target n.bits) := by
  obtain ⟨time,bound,reading⟩:=flagged_executes extra source target temporary flag st sw tw fs ft fw store scratch
  rw [flagged_result_updates extra source target temporary flag st sw tw fs ft fw store scratch] at reading
  have parsed : Encoding.unframe (store source)=some (n.bits,suffix) := by
    rw [input];exact Encoding.unframe_frame _ _
  simp only [unframeSuffix,unframePayload,parsed,Option.map_some,Option.getD_some,
    Option.isSome_some,outEmpty,List.append_nil] at reading
  let ready:=Function.update (Function.update store source suffix) target n.bits
  let flagged:=Function.update ready flag (true::store flag)
  have combining:=combineFlags_executes (extra+2) flag flagged accepted true tail (by simp [flagged,status])
  have final : Function.update flagged flag ((accepted && true)::tail)=ready := by
    simp only [flagged,Bool.and_true,Function.update_idem]
    have same : ready flag=accepted::tail := by simp [ready,fs,ft,status]
    rw [←same,Function.update_eq_self]
  rw [final] at combining
  exact ⟨time+1+3,by omega,reading.sequence combining⟩

end Counting.StackMachine.EncodingPrograms
