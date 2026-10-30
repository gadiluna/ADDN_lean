import Counting.ExternalCoverVerifierFramed

namespace Counting.External.CoverVerification
open StackMachine StackMachine.Routine StackMachine.EncodingPrograms
set_option backward.isDefEq.respectTransparency false

def verify (input : List Bool) : Bool :=
  (Encoding.unframe input).isSome && checkEncodedMask (unframePayload input) (unframeSuffix input)

def entryRoutine (extra : Nat) (w : VerifierWorkspace extra) : Routine (extra+62) :=
  sequence (ofProgram (flaggedProgram (extra+60) (w 63) (w 0) (w 3) (w 1)))
    (sequence (ofProgram (ListPrograms.copyProgram (extra+61) (w 63) (w 33) (w 3)))
      (sequence (clear (w 63)) (framedGuard extra w)))

def verifierCoefficient := 32*(guardedCoefficient+2)+20

theorem entryRoutine_executes (extra : Nat) (w : VerifierWorkspace extra)
    (store : Fin (extra+64) → List Bool)
    (empty : ∀ i : Fin 64,i≠63 → store (w i)=[]) :
    ∃ time ≤ verifierCoefficient*((store (w 63)).length+1)^5,
      ∃ result, Executes (entryRoutine extra w) store time result ∧
        result (w 1)=[verify (store (w 63))] := by
  have ne (i j : Fin 64) (h : i≠j) : w i≠w j := fun same => h (w.injective same)
  let input := store (w 63)
  obtain ⟨frameTime,frameBound,frameRun⟩ := flagged_executes (extra+60) (w 63) (w 0) (w 3) (w 1)
    (ne 63 0 (by decide)) (ne 63 3 (by decide)) (ne 0 3 (by decide))
    (ne 1 63 (by decide)) (ne 1 0 (by decide)) (ne 1 3 (by decide)) store (empty 3 (by decide))
  rw [flagged_result_updates (extra+60) (w 63) (w 0) (w 3) (w 1)
    (ne 63 0 (by decide)) (ne 63 3 (by decide)) (ne 0 3 (by decide))
    (ne 1 63 (by decide)) (ne 1 0 (by decide)) (ne 1 3 (by decide)) store (empty 3 (by decide)),
    empty 0 (by decide),empty 1 (by decide),List.append_nil] at frameRun
  let framed := Function.update (Function.update (Function.update store (w 63) (unframeSuffix input))
    (w 0) (unframePayload input)) (w 1) [(Encoding.unframe input).isSome]
  have copying := copy_executes (extra+61) (w 63) (w 33) (w 3)
    (ne 63 33 (by decide)) (ne 63 3 (by decide)) (ne 33 3 (by decide)) framed
    (by simp [framed,w.injective.eq_iff,empty])
  have framedSource : framed (w 63)=unframeSuffix input := by simp [framed,w.injective.eq_iff]
  have framedTarget : framed (w 33)=[] := by simp [framed,w.injective.eq_iff,empty]
  rw [framedSource,framedTarget,List.append_nil] at copying
  let copied := Function.update framed (w 33) (unframeSuffix input)
  have clearing := clear_executes (w 63) copied
  have copiedSource : copied (w 63)=unframeSuffix input := by simp [copied,w.injective.eq_iff,framedSource]
  rw [copiedSource] at clearing
  let ready := Function.update copied (w 63) []
  have readyEmpty (i : Fin 64) (a : i≠0) (b : i≠1) (c : i≠33) : ready (w i)=[] := by
    by_cases d : i=63
    · subst i;simp [ready]
    · simp [ready,copied,framed,w.injective.eq_iff,a,b,c,d,empty i d]
  obtain ⟨checkTime,checkBound,result,checking,output⟩ := framedGuard_executes extra w ready
    (Encoding.unframe input).isSome (by simp [ready,copied,framed,w.injective.eq_iff]) readyEmpty
  have readySource : ready (w 0)=unframePayload input := by simp [ready,copied,framed,w.injective.eq_iff]
  have readyWitness : ready (w 33)=unframeSuffix input := by simp [ready,copied,w.injective.eq_iff]
  rw [readySource,readyWitness] at checkBound output
  have combined := frameRun.sequence (copying.sequence (clearing.sequence checking))
  refine ⟨frameTime+1+(5*(unframeSuffix input).length+2+1+((unframeSuffix input).length+1+1+checkTime)),?_,
    result,combined,output⟩
  have payloadBound := unframe_payload_length input
  have suffixBound := unframe_suffix_length input
  have power : ((unframePayload input).length+(unframeSuffix input).length+1)^5≤32*(input.length+1)^5 := by
    calc
      _ ≤ (2*(input.length+1))^5 := Nat.pow_le_pow_left (by omega) 5
      _ = _ := by ring
  have checkingBound : checkTime≤32*(guardedCoefficient+2)*(input.length+1)^5 := by
    have h := checkBound.trans (Nat.mul_le_mul_left (guardedCoefficient+2) power)
    nlinarith
  have linear : input.length+1≤(input.length+1)^5 := Nat.le_self_pow (by decide) _
  change frameTime≤3*input.length+4 at frameBound
  change _≤verifierCoefficient*(input.length+1)^5
  unfold verifierCoefficient
  nlinarith

theorem verify_pairWords (input witness : List Bool) : verify (Encoding.pairWords input witness)=checkEncodedMask input witness := by
  simp [verify,Encoding.pairWords,unframePayload,unframeSuffix,Encoding.unframe_frame]

end Counting.External.CoverVerification
