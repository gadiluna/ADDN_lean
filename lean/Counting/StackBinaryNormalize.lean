import Counting.StackNormalize
import Counting.StackEncodingUnframe
import Counting.StackEncodingCanonical

namespace Counting.StackMachine.Binary
open Routine EncodingPrograms

/-- Normalize in place through the already verified canonical frame and
its actual finite parser. Both temporary registers are restored empty. -/
def normalizePayload (extra : Nat) (source frame scratch : Fin (extra+3)) : Routine (extra+1) :=
  sequence (Normalize.formatRoutine extra source frame scratch)
    (ofProgram (unframeProgram extra frame source scratch))

def normalizePayloadCost (bits : List Bool) : Nat :=
  Normalize.formatCost bits+1+(5*(Encoding.value bits).bits.length+2)

theorem normalizePayloadCost_le (bits : List Bool) : normalizePayloadCost bits ≤ 10*bits.length+7 := by
  have first := Normalize.formatCost_le bits
  have second := normalize_length_le bits
  rw [Arithmetic.normalize_eq_bits] at second
  dsimp only [normalizePayloadCost]
  omega

theorem normalizePayload_executes (extra : Nat) (source frame scratch : Fin (extra+3))
    (sf : source ≠ frame) (sw : source ≠ scratch) (fw : frame ≠ scratch)
    (store : Fin (extra+3) → List Bool) (frameEmpty : store frame = []) (scratchEmpty : store scratch = []) :
    Executes (normalizePayload extra source frame scratch) store (normalizePayloadCost (store source))
      (Function.update store source (Encoding.value (store source)).bits) := by
  let bits := (Encoding.value (store source)).bits
  let middle := Function.update (Function.update store source []) frame (Encoding.frame bits)
  have formatted := Normalize.format_executes extra source frame scratch sf sw fw store scratchEmpty
  change Executes (Normalize.formatRoutine extra source frame scratch) store (Normalize.formatCost (store source))
    (Function.update (Function.update store source []) frame (Encoding.frame bits++store frame)) at formatted
  rw [frameEmpty,List.append_nil] at formatted
  have atFrame : middle frame = Encoding.frame bits := by simp only [middle,Function.update_self]
  have atSource : middle source = [] := by simp only [middle,Function.update_of_ne sf,Function.update_self]
  have atScratch : middle scratch = [] := by
    simp only [middle,Function.update_of_ne (Ne.symm fw),Function.update_of_ne (Ne.symm sw),scratchEmpty]
  have start : unframeConfig extra frame source scratch 0 middle (Encoding.frame bits++[]) [] [] =
      (⟨0,middle⟩ : Config (unframeProgram extra frame source scratch)) := by
    apply congrArg (Config.mk _)
    funext r
    by_cases f : r=frame
    · subst r; simp [atFrame]
    · by_cases s : r=source
      · subst r; simp [f,atSource]
      · by_cases w : r=scratch
        · subst r; simp [f,s,atScratch]
        · simp [f,s,w]
  have decoded : Executes (ofProgram (unframeProgram extra frame source scratch)) middle (5*bits.length+2)
      (Function.update store source bits) := by
    refine ⟨unframeConfig extra frame source scratch 7 middle [] bits [],?_,(unframe_halted _ _ _ _ _ _ _ _).1,?_⟩
    · rw [← start]
      have executed := unframe_frames extra frame source scratch (Ne.symm sf) fw sw middle bits [] []
      simp only [List.append_nil] at executed
      simp only [List.append_nil]
      exact executed
    · change (fun r : Fin (extra+3) => if r=frame then [] else if r=source then bits else if r=scratch then [] else middle r) =
        Function.update store source bits
      funext r
      by_cases f : r=frame
      · subst r; simp [Function.update,Ne.symm sf,frameEmpty]
      · by_cases s : r=source
        · subst r; simp [f]
        · by_cases w : r=scratch
          · subst r
            simp only [if_neg f,if_neg s,ite_true,Function.update_of_ne s,scratchEmpty]
          · rw [if_neg f,if_neg s,if_neg w,Function.update_of_ne s]
            dsimp only [middle]
            rw [Function.update_of_ne f,Function.update_of_ne s]
  exact formatted.sequence decoded

end Counting.StackMachine.Binary
