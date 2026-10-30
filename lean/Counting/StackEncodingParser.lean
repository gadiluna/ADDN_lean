import Counting.StackEncodingListItem
import Counting.StackEncodingListCheck

/-! Compositional parser contracts carry concrete finite stack routines,
full-register execution proofs, and costs. A pure result function is only a
specification: its runtime is justified by the accompanying `Executes` proof. -/
namespace Counting.StackMachine.EncodingPrograms

structure ParseEffect where
  suffix : List Bool
  code : List Bool
  accepted : Bool
  deriving Repr, DecidableEq

def parseStore {registers : Nat} (source status output : Fin (registers+2))
    (store : Routine.Store registers) (accepted : Bool) (tail : List Bool) (result : ParseEffect) : Routine.Store registers :=
  fun r => if r=source then result.suffix else if r=status then (accepted && result.accepted)::tail
    else if r=output then result.code.reverse++store output else store r

/-- Scratch is explicit, allowing a child parser to preserve an enclosing
list's live counter. There is no oracle instruction or free decoder call. -/
structure VerifiedParser (registers : Nat) (source status output : Fin (registers+2))
    (α : Type) (codec : Encoding.Codec α) where
  work : Finset (Fin (registers+2))
  separate : ∀ r∈work, r≠source ∧ r≠status ∧ r≠output
  routine : Routine registers
  effect : List Bool → ParseEffect
  coefficient : Nat
  exponent : Nat
  suffix_le : ∀ input, (effect input).suffix.length ≤ input.length
  code_le : ∀ input, (effect input).code.length ≤ Complexity.polynomial coefficient exponent input.length
  sound : ∀ input, (effect input).accepted=true → ∃ value,
    codec.encode value++(effect input).suffix=input ∧ (effect input).code=codec.encode value
  roundtrip : ∀ value suffix, effect (codec.encode value++suffix)=⟨suffix,codec.encode value,true⟩
  executes : ∀ store accepted tail, store status=accepted::tail → (∀ r∈work,store r=[]) →
    ∃ time ≤ Complexity.polynomial coefficient exponent (store source).length,
      Routine.Executes routine store time (parseStore source status output store accepted tail (effect (store source)))

namespace VerifiedParser

theorem accepts_iff {registers : Nat} {source status output : Fin (registers+2)}
    {α : Type} {codec : Encoding.Codec α} (parser : VerifiedParser registers source status output α codec)
    (input : List Bool) :
    (parser.effect input).accepted=true ↔ ∃ value suffix, codec.encode value++suffix=input := by
  constructor
  · intro accepted
    obtain ⟨value,split,_⟩:=parser.sound input accepted
    exact ⟨value,_,split⟩
  · rintro ⟨value,suffix,rfl⟩
    rw [parser.roundtrip]

theorem scratch_unchanged {registers : Nat} {source status output : Fin (registers+2)}
    {α : Type} {codec : Encoding.Codec α} (parser : VerifiedParser registers source status output α codec)
    (store : Routine.Store registers) (accepted : Bool) (tail : List Bool) (result : ParseEffect)
    (r : Fin (registers+2)) (member : r∈parser.work) :
    parseStore source status output store accepted tail result r=store r := by
  obtain ⟨a,b,c⟩:=parser.separate r member
  simp [parseStore,a,b,c]

end VerifiedParser

end Counting.StackMachine.EncodingPrograms
