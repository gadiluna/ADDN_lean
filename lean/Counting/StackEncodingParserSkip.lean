import Counting.StackEncodingParserLoop
import Counting.StackRoutineBasic

/-! Skipping structured values executes their existing canonical parsers.
In particular, a variable-length node is not treated as one framed field. -/
namespace Counting.StackMachine.EncodingPrograms
open Routine
set_option backward.isDefEq.respectTransparency false

def skipEffect (effect : List Bool → ParseEffect) (count : Nat) (input : List Bool) : ParseEffect :=
  {manyEffect effect count input with code:=[]}

theorem parseStore_clear_output {registers : Nat} {source status output : Fin (registers+2)}
    (so : source≠output) (statusOutput : status≠output) (store : Store registers)
    (accepted : Bool) (tail : List Bool) (effect : ParseEffect) (empty : store output=[]) :
    Function.update (parseStore source status output store accepted tail effect) output []=
      parseStore source status output store accepted tail {effect with code:=[]} := by
  funext r
  by_cases h : r=output
  · subst r; simp [parseStore,Ne.symm so,Ne.symm statusOutput,empty]
  · simp [parseStore,h]

namespace VerifiedParser

variable {registers : Nat} {source status output : Fin (registers+2)}
  {α : Type} {codec : Encoding.Codec α}

/-- The loop retains one shared encoded prefix, then clears it once. Both the
parsers and this clearing pass are charged in the execution theorem. -/
def skip (parser : VerifiedParser registers source status output α codec)
    (counter : Fin (registers+2)) : Routine registers :=
  sequence (forEach counter parser.routine) (clear output)

theorem skip_executes (ss : source≠status) (so : source≠output) (statusOutput : status≠output)
    (parser : VerifiedParser registers source status output α codec)
    (counter : Fin (registers+2)) (cs : counter≠source) (ct : counter≠status) (co : counter≠output)
    (unused : counter∉parser.work) (bits : List Bool) (store : Store registers)
    (accepted : Bool) (tail : List Bool) (statusEq : store status=accepted::tail)
    (workEmpty : ∀ r∈parser.work,store r=[]) (outputEmpty : store output=[])
    (counterEq : store counter=bits) (limit : Nat) (inputBound : (store source).length≤limit) :
    ∃ time ≤ bits.length*(2*Complexity.polynomial parser.coefficient parser.exponent limit+2)+3,
      Executes (parser.skip counter) store time
        (parseStore source status output (Function.update store counter []) accepted tail
          (skipEffect parser.effect bits.length (store source))) := by
  obtain ⟨time,bounded,executed⟩:=parser.loop_executes ss so statusOutput counter cs ct co unused
    bits store accepted tail statusEq workEmpty counterEq limit inputBound
  let result:=parseStore source status output (Function.update store counter []) accepted tail
    (manyEffect parser.effect bits.length (store source))
  have outputValue : result output=(manyEffect parser.effect bits.length (store source)).code.reverse := by
    simp [result,parseStore,Ne.symm so,Ne.symm statusOutput,Ne.symm co,outputEmpty]
  have clearing:=clear_executes output result
  rw [outputValue,List.length_reverse,parseStore_clear_output so statusOutput _ _ _ _
    (by simp [Ne.symm co,outputEmpty])] at clearing
  have composed:=executed.sequence clearing
  refine ⟨_,?_,composed⟩
  have code:=parser.many_code_le bits.length (store source)
  have poly : Complexity.polynomial parser.coefficient parser.exponent (store source).length≤
      Complexity.polynomial parser.coefficient parser.exponent limit := by
    unfold Complexity.polynomial
    gcongr
  have codeBound:=code.trans (Nat.mul_le_mul_left bits.length poly)
  nlinarith

end VerifiedParser
end Counting.StackMachine.EncodingPrograms
