import Counting.StackGaussianTranscriptWords

namespace Counting.StackMachine.GaussianTranscript
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

theorem payload_length_le (kind : Kind) (first second : Nat) (factor : List Bool) :
    (payload kind first second factor).length ≤ 2*first+2*second+(factorWord kind factor).length+7 := by
  have firstBits : first.size ≤ first := Nat.size_le.mpr Nat.lt_two_pow_self
  have secondBits : (secondIndex kind second).size ≤ secondIndex kind second :=
    Nat.size_le.mpr Nat.lt_two_pow_self
  have secondBound : secondIndex kind second ≤ second := by cases kind <;> simp [secondIndex]
  have tagBound : (Encoding.natural.encode kind.tag).length ≤ 5 := by cases kind <;> decide
  simp only [payload,List.length_append]
  simp only [Encoding.natural_length] at tagBound ⊢
  omega

/-- Build the four fields, frame them on the reversed operation stream,
and increment its unary length. Unused swap/scale parameters are untouched. -/
def emit (kind : Kind) (extra : Nat) (w : Workspace extra) : Routine (extra+7) :=
  sequence (payloadRoutine kind extra w)
    (sequence (frameRoutine (extra+6) (w 5) (w 3) (w 8)) (pushBit (w 4) true))

def result (extra : Nat) (w : Workspace extra) (store : Fin (extra+9) → List Bool)
    (word : List Bool) : Fin (extra+9) → List Bool :=
  Function.update (Function.update store (w 3) (Encoding.frame word++store (w 3)))
    (w 4) (true::store (w 4))

theorem emit_payload_executes (kind : Kind) (extra : Nat) (w : Workspace extra)
    (store : Fin (extra+9) → List Bool) (first second : Nat)
    (firstSource : store (w 0)=List.replicate (first+1) true)
    (secondSource : kind≠.scale → store (w 1)=List.replicate (second+1) true)
    (e5 : store (w 5)=[]) (e6 : store (w 6)=[]) (e7 : store (w 7)=[]) (e8 : store (w 8)=[]) :
    ∃ time ≤ 200*(first+second+(factorWord kind (store (w 2))).length+10)^2,
      Executes (emit kind extra w) store time
        (result extra w store (payload kind first second (store (w 2)))) := by
  obtain ⟨payloadTime,payloadBound,payloadRun⟩ := payload_executes kind extra w store first second
    firstSource secondSource e5 e6 e7 e8
  let word := payload kind first second (store (w 2))
  let withPayload := Function.update store (w 5) word
  have ne (i j : Fin 9) (different : i≠j) : w i≠w j := fun same => different (w.injective same)
  have framing := frame_executes (extra+6) (w 5) (w 3) (w 8)
    (ne 5 3 (by decide)) (ne 5 8 (by decide)) (ne 3 8 (by decide)) withPayload
    (by simp [withPayload,w.injective.eq_iff,e8])
  let framed := Function.update store (w 3) (Encoding.frame word++store (w 3))
  have restored : frameResult (extra+6) (w 5) (w 3) (w 8) withPayload=framed := by
    funext register
    by_cases source : register=w 5
    · subst register;simp [frameResult,framed,w.injective.eq_iff,e5]
    · by_cases output : register=w 3
      · subst register;simp [frameResult,withPayload,framed,w.injective.eq_iff]
      · by_cases scratch : register=w 8
        · subst register;simp [frameResult,framed,w.injective.eq_iff,e8]
        · simp [frameResult,withPayload,framed,source,output,scratch]
  rw [restored] at framing
  have increment := pushBit_executes (w 4) true framed
  have count : framed (w 4)=store (w 4) := by simp [framed,w.injective.eq_iff]
  rw [count] at increment
  have combined := payloadRun.sequence (framing.sequence increment)
  have length : (withPayload (w 5)).length=word.length := by simp [withPayload]
  rw [length] at combined
  refine ⟨payloadTime+1+(5*word.length+4+1+1),?_,combined⟩
  let size := first+second+(factorWord kind (store (w 2))).length+10
  have lengthBound : word.length ≤ 2*size := by
    have bound := payload_length_le kind first second (store (w 2))
    dsimp [word,size]
    omega
  have squareLarge : size ≤ size^2 := by simpa only [pow_two] using Nat.le_mul_self size
  have positive : 1 ≤ size := by dsimp [size];omega
  change payloadTime ≤ 100*size^2 at payloadBound
  change payloadTime+1+(5*word.length+4+1+1) ≤ 200*size^2
  nlinarith only [payloadBound,lengthBound,squareLarge,positive]

theorem payload_canonical_of_factor (kind : Kind) (first second : Nat) (factor : Rat) (bits : List Bool)
    (canonical : kind≠.swap → bits=Encoding.rational.encode factor) :
    payload kind first second bits=Encoding.rawRowOp.encode (kind.operation first second factor) := by
  by_cases swap : kind=.swap
  · subst kind;simp [payload,Kind.operation,Kind.tag,secondIndex,factorWord,List.append_assoc]
  · rw [canonical swap]
    exact payload_canonical kind first second factor

/-- Each emitted record is the canonical codec of the actual row operation;
every parameter, arbitrary outside register and empty scratch is preserved. -/
theorem emit_operation_executes (kind : Kind) (extra : Nat) (w : Workspace extra)
    (store : Fin (extra+9) → List Bool) (first second : Nat) (factor : Rat)
    (firstSource : store (w 0)=List.replicate (first+1) true)
    (secondSource : kind≠.scale → store (w 1)=List.replicate (second+1) true)
    (factorSource : kind≠.swap → store (w 2)=Encoding.rational.encode factor)
    (e5 : store (w 5)=[]) (e6 : store (w 6)=[]) (e7 : store (w 7)=[]) (e8 : store (w 8)=[]) :
    ∃ time ≤ 200*(first+second+(factorWord kind (store (w 2))).length+10)^2,
      Executes (emit kind extra w) store time
        (result extra w store (Encoding.rawRowOp.encode (kind.operation first second factor))) := by
  obtain ⟨time,bounded,ran⟩ := emit_payload_executes kind extra w store first second
    firstSource secondSource e5 e6 e7 e8
  rw [payload_canonical_of_factor kind first second factor _ factorSource] at ran
  exact ⟨time,bounded,ran⟩

end Counting.StackMachine.GaussianTranscript
