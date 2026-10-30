import Counting.StackEncodingFrameStore
import Counting.StackEncodingPair

namespace Counting.StackMachine.EncodingPrograms

set_option backward.isDefEq.respectTransparency false

abbrev ListWorkspace (extra : Nat) := Fin 8 ↪ Fin (extra+8)

/-- Roles: input, payload, scratch, accumulated status, canonicality work,
encoded item, reversed list body, unary item counter. -/
def listItem (extra : Nat) (w : ListWorkspace extra) : Routine (extra+6) :=
  Routine.sequence (Routine.ofProgram (flaggedProgram (extra+4) (w 0) (w 1) (w 2) (w 3)))
    (Routine.sequence (Routine.ofProgram (ListPrograms.copyProgram (extra+5) (w 1) (w 4) (w 2)))
      (Routine.sequence (Routine.ofProgram (canonicalProgram (extra+6) (w 4) (w 3)))
        (Routine.sequence (Routine.ofProgram (combineFlagsProgram (extra+6) (w 3)))
          (Routine.sequence (Routine.ofProgram (combineFlagsProgram (extra+6) (w 3)))
            (Routine.sequence (frameRoutine (extra+5) (w 1) (w 5) (w 2))
              (Routine.ofProgram (ListPrograms.reverseProgram (extra+6) (w 5) (w 6))))))))

def itemAccepted (input : List Bool) : Bool :=
  (Encoding.unframe input).isSome && canonicalPayload (unframePayload input)

def listItemResult (extra : Nat) (w : ListWorkspace extra) (store : Fin (extra+8) → List Bool)
    (accepted : Bool) (tail : List Bool) : Fin (extra+8) → List Bool :=
  Function.update
    (Function.update (Function.update store (w 0) (unframeSuffix (store (w 0)))) (w 3)
      ((accepted && itemAccepted (store (w 0)))::tail)) (w 6)
      ((Encoding.frame (unframePayload (store (w 0)))).reverse++store (w 6))

/-- One charged parsing iteration. Canonicality, aggregate validity, output
framing, and output reversal are all actual finite stack routines. All work
registers are restored, even if the frame is truncated or noncanonical. -/
theorem listItem_executes (extra : Nat) (w : ListWorkspace extra)
    (store : Fin (extra+8) → List Bool) (accepted : Bool) (tail : List Bool)
    (status : store (w 3)=accepted::tail)
    (payloadEmpty : store (w 1)=[]) (scratchEmpty : store (w 2)=[])
    (canonicalEmpty : store (w 4)=[]) (encodedEmpty : store (w 5)=[]) :
    ∃ time ≤ 20*(store (w 0)).length+40,
      Routine.Executes (listItem extra w) store time (listItemResult extra w store accepted tail) := by
  have ne (i j : Fin 8) (different : i≠j) : w i≠w j := fun equal => different (w.injective equal)
  let payload := unframePayload (store (w 0))
  let suffix := unframeSuffix (store (w 0))
  let ok := (Encoding.unframe (store (w 0))).isSome
  let parsed := Function.update (Function.update (Function.update store (w 0) suffix) (w 1) payload) (w 3) (ok::store (w 3))
  obtain ⟨parseTime,parseBound,parseRun⟩ := flagged_executes (extra+4) (w 0) (w 1) (w 2) (w 3)
    (ne 0 1 (by decide)) (ne 0 2 (by decide)) (ne 1 2 (by decide))
    (ne 3 0 (by decide)) (ne 3 1 (by decide)) (ne 3 2 (by decide)) store scratchEmpty
  have parsing : Routine.Executes (Routine.ofProgram (flaggedProgram (extra+4) (w 0) (w 1) (w 2) (w 3)))
      store parseTime parsed := by
    rw [flagged_result_updates (extra+4) (w 0) (w 1) (w 2) (w 3)
      (ne 0 1 (by decide)) (ne 0 2 (by decide)) (ne 1 2 (by decide))
      (ne 3 0 (by decide)) (ne 3 1 (by decide)) (ne 3 2 (by decide)) store scratchEmpty,
      payloadEmpty,List.append_nil] at parseRun
    exact parseRun
  have parsedAt (i : Fin 8) (a : i≠0) (b : i≠1) (c : i≠3) : parsed (w i)=store (w i) := by
    simp only [parsed,Function.update_of_ne (ne i 3 c),Function.update_of_ne (ne i 1 b),Function.update_of_ne (ne i 0 a)]
  have parsedPayload : parsed (w 1)=payload := by simp [parsed,w.injective.eq_iff]
  have parsedStatus : parsed (w 3)=ok::store (w 3) := by simp [parsed]
  let copied := Function.update parsed (w 4) payload
  have copying : Routine.Executes (Routine.ofProgram (ListPrograms.copyProgram (extra+5) (w 1) (w 4) (w 2)))
      parsed (5*payload.length+2) copied := by
    have run := Routine.copy_executes (extra+5) (w 1) (w 4) (w 2)
      (ne 1 4 (by decide)) (ne 1 2 (by decide)) (ne 4 2 (by decide)) parsed
      ((parsedAt 2 (by decide) (by decide) (by decide)).trans scratchEmpty)
    simpa only [ListPrograms.copyProgram,parsedPayload,parsedAt 4 (by decide) (by decide) (by decide),canonicalEmpty,List.append_nil] using run
  have clearedCopy : Function.update copied (w 4) []=parsed := by
    simp only [copied,Function.update_idem]
    rw [← (parsedAt 4 (by decide) (by decide) (by decide)).trans canonicalEmpty,Function.update_eq_self]
  let checked := Function.update parsed (w 3) (canonicalPayload payload::ok::store (w 3))
  have canonical : Routine.Executes (Routine.ofProgram (canonicalProgram (extra+6) (w 4) (w 3)))
      copied (payload.length+2) checked := by
    have run := canonical_executes (extra+6) (w 4) (w 3) (ne 4 3 (by decide)) copied
    simp only [copied,Function.update_self] at run
    rw [clearedCopy] at run
    simpa only [Function.update_of_ne (ne 3 4 (by decide)),parsedStatus] using run
  let firstStatus := Function.update parsed (w 3) ((ok && canonicalPayload payload)::store (w 3))
  have firstCombine : Routine.Executes (Routine.ofProgram (combineFlagsProgram (extra+6) (w 3))) checked 3 firstStatus := by
    have run := combineFlags_executes (extra+6) (w 3) checked ok (canonicalPayload payload) (store (w 3)) (by simp [checked])
    simpa only [checked,Function.update_idem] using run
  let finalStatus := Function.update parsed (w 3) ((accepted && (ok && canonicalPayload payload))::tail)
  have secondCombine : Routine.Executes (Routine.ofProgram (combineFlagsProgram (extra+6) (w 3))) firstStatus 3 finalStatus := by
    have run := combineFlags_executes (extra+6) (w 3) firstStatus accepted (ok && canonicalPayload payload) tail (by simp [firstStatus,status])
    simpa only [firstStatus,Function.update_idem] using run
  have finalPayload : finalStatus (w 1)=payload := by simp [finalStatus,parsed,w.injective.eq_iff]
  have finalScratch : finalStatus (w 2)=[] := by simp [finalStatus,parsed,w.injective.eq_iff,scratchEmpty]
  have finalEncoded : finalStatus (w 5)=[] := by simp [finalStatus,parsed,w.injective.eq_iff,encodedEmpty]
  let framed := Function.update (Function.update finalStatus (w 1) []) (w 5) (Encoding.frame payload)
  have framing : Routine.Executes (frameRoutine (extra+5) (w 1) (w 5) (w 2)) finalStatus
      (5*payload.length+4) framed := by
    have run := frame_executes_updates (extra+5) (w 1) (w 5) (w 2)
      (ne 1 5 (by decide)) (ne 1 2 (by decide)) (ne 5 2 (by decide)) finalStatus finalScratch
    simpa only [finalPayload,finalEncoded,List.append_nil] using run
  have frameValue : framed (w 5)=Encoding.frame payload := by simp [framed]
  have oldOutput : framed (w 6)=store (w 6) := by simp [framed,finalStatus,parsed,w.injective.eq_iff]
  have reversing := Routine.reverse_executes (extra+6) (w 5) (w 6) (ne 5 6 (by decide)) framed
  rw [frameValue,oldOutput] at reversing
  have restored : Function.update (Function.update framed (w 5) []) (w 6)
      ((Encoding.frame payload).reverse++store (w 6)) = listItemResult extra w store accepted tail := by
    funext r
    by_cases a : r=w 1
    · subst r; simp [framed,finalStatus,parsed,listItemResult,w.injective.eq_iff,payloadEmpty]
    · by_cases b : r=w 5
      · subst r; simp [framed,finalStatus,parsed,listItemResult,w.injective.eq_iff,encodedEmpty]
      · simp [framed,finalStatus,parsed,listItemResult,payload,suffix,ok,itemAccepted,Function.update_apply,a,b]
  rw [restored] at reversing
  have composed := parsing.sequence (copying.sequence (canonical.sequence (firstCombine.sequence (secondCombine.sequence (framing.sequence reversing)))))
  refine ⟨parseTime+15*payload.length+23,?_,?_⟩
  · have size := unframe_payload_length (store (w 0))
    change payload.length≤(store (w 0)).length at size
    omega
  · simp only [Encoding.frame_length] at composed
    convert composed using 1 <;> first | rfl | omega

end Counting.StackMachine.EncodingPrograms
