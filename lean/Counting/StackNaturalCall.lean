import Counting.StackRoutineClean
import Counting.StackNormalize
import Counting.StackEncodingUnframe

namespace Counting.StackMachine.NaturalCall
open Routine

set_option backward.isDefEq.respectTransparency false

/-- Three public registers followed by ten private machine registers. -/
def file (first second output input encoded work temp : List Bool) : Fin 13 → List Bool :=
  ![first,second,output,input,encoded,work,temp,[],[],[],[],[],[]]

def sourceIndex (second : Bool) : Fin 13 := if second then 1 else 0
abbrev prependMagnitude (second : Bool) : Routine 11 := sequence
  (ofProgram (ListPrograms.copyProgram 10 (sourceIndex second) 5 6))
  (Normalize.formatRoutine 10 5 3 6)
abbrev prepare : Routine 11 := sequence (prependMagnitude true) (prependMagnitude false)

def addresses : Fin 10 ↪ Fin 13 := ⟨fun index => ⟨index.val+3,by omega⟩,
  by intro a b equal; apply Fin.ext; have := congrArg (fun index : Fin 13 => index.val) equal; dsimp at this; omega⟩

abbrev decodeOutput : Routine 11 := ofProgram (EncodingPrograms.unframeProgram 10 4 2 5)
abbrev callNatural (routine : Routine 8) : Routine 11 :=
  sequence prepare (sequence (relocate (isolate routine) addresses) decodeOutput)

theorem prepend_executes (chooseSecond : Bool) (first second suffix : List Bool) :
    ∃ time ≤ 10*(if chooseSecond then second else first).length+7,
      Executes (prependMagnitude chooseSecond) (file first second [] suffix [] [] []) time
        (file first second []
          (Encoding.natural.encode (Encoding.value (if chooseSecond then second else first))++suffix) [] [] []) := by
  have sourceWork : sourceIndex chooseSecond ≠ 5 := by cases chooseSecond <;> decide
  have sourceTemp : sourceIndex chooseSecond ≠ 6 := by cases chooseSecond <;> decide
  let operand := if chooseSecond then second else first
  have sourceAt : file first second [] suffix [] [] [] (sourceIndex chooseSecond) = operand := by cases chooseSecond <;> rfl
  have copied := copy_executes 10 (sourceIndex chooseSecond) 5 6 sourceWork sourceTemp (by decide)
    (file first second [] suffix [] [] []) rfl
  change Executes (ofProgram (ListPrograms.copyProgram 10 (sourceIndex chooseSecond) 5 6))
    (file first second [] suffix [] [] []) (5*(file first second [] suffix [] [] [] (sourceIndex chooseSecond)).length+2)
    (Function.update (file first second [] suffix [] [] []) 5
      (file first second [] suffix [] [] [] (sourceIndex chooseSecond)++[])) at copied
  rw [sourceAt] at copied
  have copyStore : Function.update (file first second [] suffix [] [] []) 5 (operand++[]) =
      file first second [] suffix [] operand [] := by
    funext r; fin_cases r <;> simp [file]
  simp +instances only [ListPrograms.copyProgram] at copied
  rw [copyStore] at copied
  have formatted := Normalize.format_executes 10 5 3 6 (by decide) (by decide) (by decide)
    (file first second [] suffix [] operand []) rfl
  change Executes (Normalize.formatRoutine 10 5 3 6) (file first second [] suffix [] operand [])
    (Normalize.formatCost operand)
    (Function.update (Function.update (file first second [] suffix [] operand []) 5 []) 3
      (Encoding.natural.encode (Encoding.value operand)++suffix)) at formatted
  have formatStore : Function.update (Function.update (file first second [] suffix [] operand []) 5 []) 3
      (Encoding.natural.encode (Encoding.value operand)++suffix) =
      file first second [] (Encoding.natural.encode (Encoding.value operand)++suffix) [] [] [] := by
    funext r; fin_cases r <;> rfl
  rw [formatStore] at formatted
  refine ⟨_,?_,copied.sequence formatted⟩
  have bound := Normalize.formatCost_le operand
  change _ ≤ 10*operand.length+7
  omega

def arguments (first second : List Bool) : List Bool :=
  (Encoding.product Encoding.natural Encoding.natural).encode (Encoding.value first,Encoding.value second)

theorem prepare_executes (first second : List Bool) :
    ∃ time ≤ 10*(first.length+second.length)+15,
      Executes prepare (file first second [] [] [] [] []) time
        (file first second [] (arguments first second) [] [] []) := by
  obtain ⟨secondTime,secondBound,secondRan⟩ := prepend_executes true first second []
  obtain ⟨firstTime,firstBound,firstRan⟩ := prepend_executes false first second
    (Encoding.natural.encode (Encoding.value second))
  simp only [ite_true,List.append_nil] at secondRan secondBound
  simp only [Bool.false_eq_true,ite_false] at firstRan firstBound
  exact ⟨_,by omega,secondRan.sequence firstRan⟩

theorem decode_executes (first second : List Bool) (result : Nat) :
    Executes decodeOutput (file first second [] [] (Encoding.natural.encode result) [] [])
      (5*result.bits.length+2) (file first second result.bits [] [] [] []) := by
  let base := file first second [] [] (Encoding.natural.encode result) [] []
  have start : EncodingPrograms.unframeConfig 10 4 2 5 0 base (Encoding.frame result.bits++[]) [] [] =
      (⟨0,base⟩ : Config (EncodingPrograms.unframeProgram 10 4 2 5)) := by
    apply congrArg (Config.mk _)
    change (fun r : Fin 13 => _) = base
    funext r; fin_cases r <;> simp [base,file,Encoding.natural]
  have ran := EncodingPrograms.unframe_frames 10 4 2 5 (by decide) (by decide) (by decide)
    base result.bits [] []
  rw [start] at ran
  refine ⟨EncodingPrograms.unframeConfig 10 4 2 5 7 base [] (result.bits++[]) [],ran,
    (EncodingPrograms.unframe_halted _ _ _ _ _ _ _ _).1,?_⟩
  change (fun r : Fin 13 => _) = _
  funext r; fin_cases r <;> simp [EncodingPrograms.unframeConfig,base,file]

/-- Invoke a real ten-register arithmetic program as a reusable operation
on raw magnitudes. Both operands are preserved, the result is canonical,
and every private register is empty on return. Framing, cleanup, and
unframing all contribute to the bound. -/
theorem call_executes (routine : Routine 8) (function : List Bool → List Bool)
    (bound : Nat → Nat) (computes : ComputesIn routine.program function bound)
    (operation : Nat → Nat → Nat)
    (correct : ∀ first second, function ((Encoding.product Encoding.natural Encoding.natural).encode (first,second)) =
      Encoding.natural.encode (operation first second)) (first second : List Bool) :
    ∃ time ≤ 30*(bound (arguments first second).length+(arguments first second).length+first.length+second.length+10),
      Executes (callNatural routine) (file first second [] [] [] [] []) time
        (file first second (operation (Encoding.value first) (Encoding.value second)).bits [] [] [] []) := by
  obtain ⟨prepareTime,prepareBound,prepared⟩ := prepare_executes first second
  obtain ⟨callTime,callBound,called⟩ := isolate_executes routine function bound computes (arguments first second)
  have functionResult : function (arguments first second) = Encoding.natural.encode (operation (Encoding.value first) (Encoding.value second)) := correct _ _
  rw [functionResult] at called
  let result := operation (Encoding.value first) (Encoding.value second)
  have restricted : (file first second [] (arguments first second) [] [] []) ∘ addresses =
      inputStore 8 (arguments first second) := by
    funext r; fin_cases r <;> rfl
  have executed := relocate_executes (isolate routine) addresses
    (file first second [] (arguments first second) [] [] []) callTime
    (outputStore 8 (Encoding.natural.encode result)) (by rw [restricted]; exact called)
  have resultingStore : relocatedStore addresses (file first second [] (arguments first second) [] [] [])
      (outputStore 8 (Encoding.natural.encode result)) =
      file first second [] [] (Encoding.natural.encode result) [] [] := by
    funext r
    fin_cases r
    all_goals first
    | apply relocatedStore_outside; intro source; apply Fin.ne_of_val_ne; dsimp [addresses]; omega
    | exact relocatedStore_at addresses _ _ ⟨0,by decide⟩
    | exact relocatedStore_at addresses _ _ ⟨1,by decide⟩
    | exact relocatedStore_at addresses _ _ ⟨2,by decide⟩
    | exact relocatedStore_at addresses _ _ ⟨3,by decide⟩
    | exact relocatedStore_at addresses _ _ ⟨4,by decide⟩
    | exact relocatedStore_at addresses _ _ ⟨5,by decide⟩
    | exact relocatedStore_at addresses _ _ ⟨6,by decide⟩
    | exact relocatedStore_at addresses _ _ ⟨7,by decide⟩
    | exact relocatedStore_at addresses _ _ ⟨8,by decide⟩
    | exact relocatedStore_at addresses _ _ ⟨9,by decide⟩
  rw [resultingStore] at executed
  have decoded := decode_executes first second result
  refine ⟨_,?_,prepared.sequence (executed.sequence decoded)⟩
  have outputBound := computed_length_le routine function bound computes (arguments first second)
  rw [functionResult] at outputBound
  change (Encoding.natural.encode result).length ≤ _ at outputBound
  rw [Encoding.natural_length,← Encoding.bits_length] at outputBound
  omega

end Counting.StackMachine.NaturalCall
