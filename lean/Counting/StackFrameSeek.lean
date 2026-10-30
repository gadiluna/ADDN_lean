import Counting.StackFrameSkip

namespace Counting.StackMachine.FieldAccess
open Routine

def skipMany : Nat → List Bool → List Bool
  | 0, input => input
  | count+1, input => skipMany count (skipRest input)

def scanCost : Nat → List Bool → Nat
  | 0, _ => 1
  | count+1, input => skipCost input+2+scanCost count (skipRest input)

@[simp] theorem skipMany_empty (count : Nat) : skipMany count []=[] := by
  induction count with
  | zero => rfl
  | succ count ih => exact ih

theorem skipMany_length (count : Nat) (input : List Bool) :
    (skipMany count input).length ≤ input.length := by
  induction count generalizing input with
  | zero => exact le_rfl
  | succ count ih => exact (ih (skipRest input)).trans (skipRest_length input)

theorem skipMany_naturals (count : Nat) (values : List Nat) :
    skipMany count (Encoding.sequence Encoding.natural values)=
      Encoding.sequence Encoding.natural (values.drop count) := by
  induction count generalizing values with
  | zero => rfl
  | succ count ih =>
      cases values with
      | nil => simp [Encoding.sequence]
      | cons value values =>
          simp only [skipMany,Encoding.sequence,Encoding.natural,skipRest_frame,List.drop_succ_cons]
          exact ih values

def selectPayload (input : List Bool) (index : Nat) : Option (List Bool) :=
  (Encoding.unframe (skipMany index input)).map (·.1)

theorem selectPayload_naturals (values : List Nat) (index : Nat) :
    selectPayload (Encoding.sequence Encoding.natural values) index =
      (values[index]?).map Nat.bits := by
  rw [selectPayload,skipMany_naturals,←List.head?_drop]
  cases values.drop index with
  | nil => rfl
  | cons value values => simp [Encoding.sequence,Encoding.natural,Encoding.unframe_frame]

theorem selectPayload_naturalList (values : List Nat) (index : Nat) :
    selectPayload ((Encoding.list Encoding.natural).encode values) (index+1)=
      (values[index]?).map Nat.bits := by
  change (Encoding.unframe (skipMany index (skipRest
    (Encoding.frame values.length.bits++Encoding.sequence Encoding.natural values)))).map (·.1)=_
  rw [skipRest_frame]
  exact selectPayload_naturals values index

theorem scanCost_le (count : Nat) (input : List Bool) :
    scanCost count input ≤ input.length+3*count+1 := by
  induction count generalizing input with
  | zero => simp [scanCost]
  | succ count ih =>
      have next := ih (skipRest input)
      have current := skipCost_amortized input
      simp only [scanCost]
      omega

def scanBody (source : Fin (extra+2)) (store : Store extra) : Store extra :=
  Function.update store source (skipRest (store source))

theorem scanIteration_source (source counter : Fin (extra+2)) (distinct : source≠counter)
    (store : Store extra) : iteration counter (scanBody source) store source=skipRest (store source) := by
  simp [iteration,scanBody,consume,distinct]

theorem scanIteration_counter (source counter : Fin (extra+2)) (distinct : source≠counter)
    (store : Store extra) : iteration counter (scanBody source) store counter=(store counter).tail := by
  simp [iteration,scanBody,consume,Ne.symm distinct]

theorem scanIteration_other (source counter r : Fin (extra+2))
    (rs : r≠source) (rc : r≠counter) (store : Store extra) :
    iteration counter (scanBody source) store r=store r := by
  simp [iteration,scanBody,consume,rs,rc]

theorem scan_iteration (source counter : Fin (extra+2)) (distinct : source≠counter)
    (count : Nat) (store : Store extra) :
    (iteration counter (scanBody source))^[count] store =
      Function.update (Function.update store counter ((store counter).drop count))
        source (skipMany count (store source)) := by
  induction count generalizing store with
  | zero => simp [skipMany]
  | succ count ih =>
      rw [Function.iterate_succ_apply,ih,scanIteration_source source counter distinct,
        scanIteration_counter source counter distinct]
      funext r
      by_cases atSource : r=source
      · subst r; simp [skipMany]
      · by_cases atCounter : r=counter
        · subst r
          simp [Ne.symm distinct,List.drop_tail]
        · simp [Function.update_of_ne atSource,Function.update_of_ne atCounter,
            scanIteration_other source counter r atSource atCounter]

theorem scan_time (source counter : Fin (extra+2)) (distinct : source≠counter)
    (count : Nat) (store : Store extra) :
    loopTime counter (scanBody source) (fun state => skipCost (state source)) count store =
      scanCost count (store source) := by
  induction count generalizing store with
  | zero => rfl
  | succ count ih =>
      rw [loopTime,ih,scanIteration_source source counter distinct]
      simp [consume,distinct,scanCost]

/-- Seek past a runtime number of framed fields. Both source and counter
are consumed, every other register is preserved, and the whole scan is linear
in the source bit length plus the unary index length. -/
theorem seek_executes (extra : Nat) (source counter : Fin (extra+2)) (distinct : source≠counter)
    (store : Store extra) :
    Executes (forEach counter (ofProgram (skipProgram extra source))) store
      (scanCost (store counter).length (store source))
      (Function.update (Function.update store counter []) source
        (skipMany (store counter).length (store source))) := by
  have run := forEach_executes counter (ofProgram (skipProgram extra source)) (scanBody source)
    (fun state => skipCost (state source)) (fun state => skip_executes extra source state)
    (fun state => by simp [scanBody,Ne.symm distinct]) (store counter).length store rfl
  rw [scan_time source counter distinct,scan_iteration source counter distinct] at run
  simpa only [List.drop_length] using run

end Counting.StackMachine.FieldAccess
