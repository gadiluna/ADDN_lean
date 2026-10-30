import Counting.ExternalCoverNormalizePrevious
import Counting.StackEmitNatural

namespace Counting.External.CoverNormalization
open StackMachine StackMachine.Routine
set_option backward.isDefEq.respectTransparency false

/-- Unary source, reverse output, temporary encoded word, counter, payload,
scratch. The source is bounded by the explicitly listed universe. -/
abbrev EmitWorkspace (extra : Nat) := Fin 6 ↪ Fin (extra+6)

def emitNaturalRoles (w : EmitWorkspace extra) : PowerWorkspace (extra+1) :=
  (⟨![0,2,3,4,5],by decide⟩ : Fin 5 ↪ Fin 6).trans w

def emitReversedNatural (extra : Nat) (w : EmitWorkspace extra) : Routine (extra+4) :=
  sequence (emitNatural (extra+1) (emitNaturalRoles w))
    (ofProgram (ListPrograms.reverseProgram (extra+4) (w 2) (w 1)))

theorem emitReversedNatural_executes (extra : Nat) (w : EmitWorkspace extra)
    (store : Fin (extra+6) → List Bool)
    (empty : ∀ i∈([2,3,4,5] : List (Fin 6)),store (w i)=[]) :
    ∃ time ≤ 30*((store (w 0)).length+1)^2,
      Executes (emitReversedNatural extra w) store time
        (Function.update store (w 1)
          ((Encoding.natural.encode (store (w 0)).length).reverse++store (w 1))) := by
  obtain ⟨emitTime,emitBound,emitting⟩ := emitNatural_executes (extra+1) (emitNaturalRoles w) store
    (by simp [emitNaturalRoles,empty]) (by simp [emitNaturalRoles,empty])
    (by simp [emitNaturalRoles,empty])
  let word := Encoding.natural.encode (store (w 0)).length
  let encoded := Function.update store (w 2) word
  have emitAs : Executes (emitNatural (extra+1) (emitNaturalRoles w)) store emitTime encoded := by
    simpa [emitNaturalRoles,empty,encoded,word] using emitting
  have reversing := reverse_executes (extra+4) (w 2) (w 1)
    (by simp [w.injective.eq_iff]) encoded
  have wordAt : encoded (w 2)=word := by simp [encoded]
  rw [wordAt] at reversing
  have final : Function.update (Function.update encoded (w 2) []) (w 1)
      (word.reverse++encoded (w 1))=
      Function.update store (w 1) (word.reverse++store (w 1)) := by
    funext r
    by_cases e2 : r=w 2
    · subst r;simp [w.injective.eq_iff,empty]
    · simp [encoded,e2,Function.update_apply,w.injective.eq_iff]
  rw [final] at reversing
  refine ⟨emitTime+1+(2*word.length+1),?_,emitAs.sequence reversing⟩
  change emitTime ≤ 20*((store (w 0)).length+1)^2 at emitBound
  have size : (store (w 0)).length.size ≤ (store (w 0)).length :=
    Nat.size_le.mpr Nat.lt_two_pow_self
  have wordLength : word.length=2*(store (w 0)).length.size+1 := Encoding.natural_length _
  nlinarith

end Counting.External.CoverNormalization
