import Counting.StackDagIncrement
import Counting.StackUnframeCanonical
import Counting.StackEncodingFrameStore
import Counting.StackRoutineFixedPrefix
import Counting.StackMatrixSwapBounds
import Counting.GaussianEquationCheck

namespace Counting.StackMachine.GaussianAugmentVector
open Routine EncodingPrograms

private theorem sequence_append {α:Type} (codec : Encoding.Codec α) (left right : List α) :
    Encoding.sequence codec (left++right)=Encoding.sequence codec left++Encoding.sequence codec right := by
  induction left with
  | nil => rfl
  | cons value rest ih => simp only [List.cons_append,Encoding.sequence,ih,List.append_assoc]

def file (source output header : List Bool) : Fin 5 → List Bool := ![source,output,header,[],[]]
abbrev routine : Routine 3 := sequence (ofProgram (unframeProgram 2 0 2 3))
  (sequence (prepend 1 (Encoding.frame (Encoding.rational.encode (-1))))
    (sequence (move 2 0 1 3) (sequence (DagValidation.incrementRoutine 2 4 2 3)
      (frameRoutine 2 2 1 3))))

/-- The solution's binary length header is read and incremented, and the
last field is physically appended before the new header is emitted. -/
theorem executes (values : List Rat) :
    ∃ time ≤ 100*((Encoding.rationalRow.encode values).length+1),
      Executes routine (file (Encoding.rationalRow.encode values) [] []) time
        (file [] (Encoding.rationalRow.encode (GaussianEquationCheck.vector values)) []) := by
  let fields := Encoding.sequence (Encoding.framed Encoding.rational) values
  let last := Encoding.frame (Encoding.rational.encode (-1))
  let input := file (Encoding.rationalRow.encode values) [] []
  let parsed := file fields [] values.length.bits
  let seeded := file fields last values.length.bits
  let moved := file [] (fields++last) values.length.bits
  let incremented := file [] (fields++last) (values.length+1).bits
  have a := unframe_canonical_executes 2 (0:Fin 5) 2 3 (by decide) (by decide) (by decide)
    input values.length.bits fields rfl rfl
  have aStore : Function.update (Function.update input 0 fields) 2 (values.length.bits++[])=parsed := by
    funext r;fin_cases r <;> simp [input,parsed,file]
  change Executes _ input (5*values.length.bits.length+2)
    (Function.update (Function.update input 0 fields) 2 (values.length.bits++[])) at a
  rw [aStore] at a
  have b := prepend_executes (registers:=3) 1 last parsed
  have bStore : Function.update parsed 1 (last++parsed 1)=seeded := by
    funext r;fin_cases r <;> simp [parsed,seeded,file]
  rw [bStore] at b
  have c := move_executes 2 (0:Fin 5) 1 3 (by decide) (by decide) (by decide) seeded rfl
  have cStore : Function.update (Function.update seeded 1 (seeded 0++seeded 1)) 0 []=moved := by
    funext r;fin_cases r <;> simp [seeded,moved,file]
  rw [cStore] at c
  change Executes _ seeded (6*fields.length+4) moved at c
  obtain ⟨incrementTime,incrementBound,d⟩ := DagValidation.increment_natural 2 (4:Fin 5) 2 3
    (by decide) (by decide) (by decide) moved rfl rfl values.length rfl
  have dStore : Function.update moved 2 (values.length+1).bits=incremented := by
    funext r;fin_cases r <;> simp [moved,incremented,file]
  rw [dStore] at d
  have e := frame_executes 2 (2:Fin 5) 1 3 (by decide) (by decide) (by decide) incremented rfl
  have output : frameResult 2 2 1 3 incremented=
      file [] (Encoding.rationalRow.encode (GaussianEquationCheck.vector values)) [] := by
    have fieldsAppend : Encoding.sequence (Encoding.framed Encoding.rational) (values++[-1])=fields++last := by
      simp only [sequence_append,Encoding.sequence,Encoding.framed,List.append_nil,fields,last]
    funext r;fin_cases r <;> simp [frameResult,incremented,file,GaussianEquationCheck.vector,
      Encoding.rationalRow,Encoding.list,Encoding.natural,fieldsAppend]
  rw [output] at e
  change Executes _ incremented (5*(values.length+1).bits.length+4) _ at e
  have countBound := Encoding.framedList_count_le Encoding.rational values
  have bitsBound : values.length.size≤ values.length := Nat.size_le.mpr Nat.lt_two_pow_self
  have nextBits : (values.length+1).size≤ values.length+1 := Nat.size_le.mpr Nat.lt_two_pow_self
  have inputLength : (Encoding.rationalRow.encode values).length=2*values.length.size+1+fields.length := by
    change (Encoding.natural.encode values.length++fields).length=_
    simp [Encoding.natural_length]
  have lastLength : last.length=15 := by decide
  refine ⟨_,?_,a.sequence (b.sequence (c.sequence (d.sequence e)))⟩
  simp only [Encoding.bits_length]
  rw [lastLength]
  change values.length≤ (Encoding.rationalRow.encode values).length at countBound
  omega

end Counting.StackMachine.GaussianAugmentVector
