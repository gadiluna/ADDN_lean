import Counting.StackFrameSeek

namespace Counting.StackMachine.FieldAccess
open Routine EncodingPrograms

set_option backward.isDefEq.respectTransparency false

/-- Source, unary index, payload output, empty scratch, presence flag. -/
def readField (extra : Nat) (w : Fin 5 ↪ Fin (extra+5)) : Routine (extra+3) :=
  sequence (forEach (w 1) (ofProgram (skipProgram (extra+3) (w 0))))
    (ofProgram (flaggedProgram (extra+1) (w 0) (w 2) (w 3) (w 4)))

def seekStore (extra : Nat) (w : Fin 5 ↪ Fin (extra+5))
    (store : Fin (extra+5) → List Bool) : Fin (extra+5) → List Bool :=
  Function.update (Function.update store (w 1) []) (w 0)
    (skipMany (store (w 1)).length (store (w 0)))

def readResult (extra : Nat) (w : Fin 5 ↪ Fin (extra+5))
    (store : Fin (extra+5) → List Bool) : Fin (extra+5) → List Bool :=
  flaggedResult (extra+1) (w 0) (w 2) (w 3) (w 4) (seekStore extra w store)

theorem readField_executes (extra : Nat) (w : Fin 5 ↪ Fin (extra+5))
    (store : Fin (extra+5) → List Bool) (empty : store (w 3)=[]) :
    ∃ time ≤ 4*(store (w 0)).length+3*(store (w 1)).length+6,
      Executes (readField extra w) store time (readResult extra w store) := by
  have distinct (i j : Fin 5) (h : i≠j) : w i≠w j := fun eq => h (w.injective eq)
  have sought := seek_executes (extra+3) (w 0) (w 1) (distinct 0 1 (by decide)) store
  change Executes (forEach (w 1) (ofProgram (skipProgram (extra+3) (w 0)))) store
    (scanCost (store (w 1)).length (store (w 0))) (seekStore extra w store) at sought
  obtain ⟨time,bound,read⟩ := flagged_executes (extra+1) (w 0) (w 2) (w 3) (w 4)
    (distinct 0 2 (by decide)) (distinct 0 3 (by decide)) (distinct 2 3 (by decide))
    (distinct 4 0 (by decide)) (distinct 4 2 (by decide)) (distinct 4 3 (by decide))
    (seekStore extra w store) (by simp [seekStore,w.injective.eq_iff,empty])
  refine ⟨_,?_,sought.sequence read⟩
  have scan := scanCost_le (store (w 1)).length (store (w 0))
  have suffix := skipMany_length (store (w 1)).length (store (w 0))
  simp only [seekStore,Function.update_self] at bound
  omega

theorem readResult_payload (extra : Nat) (w : Fin 5 ↪ Fin (extra+5))
    (store : Fin (extra+5) → List Bool) :
    readResult extra w store (w 2)=
      (selectPayload (store (w 0)) (store (w 1)).length).getD []++store (w 2) := by
  unfold readResult flaggedResult
  simp only [seekStore,Function.update_self]
  cases parsed : Encoding.unframe (skipMany (store (w 1)).length (store (w 0))) with
  | none => simp [selectPayload,parsed,parserStore,w.injective.eq_iff]
  | some pair =>
      obtain ⟨payload,suffix⟩:=pair
      simp [selectPayload,parsed,parserStore,w.injective.eq_iff]

theorem readResult_status (extra : Nat) (w : Fin 5 ↪ Fin (extra+5))
    (store : Fin (extra+5) → List Bool) :
    readResult extra w store (w 4)=
      (selectPayload (store (w 0)) (store (w 1)).length).isSome::store (w 4) := by
  rw [readResult,flagged_result_flag]
  simp [seekStore,w.injective.eq_iff,selectPayload]

theorem readResult_source_length (extra : Nat) (w : Fin 5 ↪ Fin (extra+5))
    (store : Fin (extra+5) → List Bool) :
    (readResult extra w store (w 0)).length ≤ (store (w 0)).length := by
  unfold readResult flaggedResult
  simp only [seekStore,Function.update_self]
  cases parsed : Encoding.unframe (skipMany (store (w 1)).length (store (w 0))) with
  | none => simp [parserStore,w.injective.eq_iff]
  | some pair =>
      obtain ⟨payload,suffix⟩:=pair
      have split := Machine.unframe_sound _ _ _ parsed
      have bound := skipMany_length (store (w 1)).length (store (w 0))
      rw [split,List.length_append] at bound
      simp only [Function.update_of_ne (fun eq => (by decide : (0:Fin 5)≠4) (w.injective eq)),parserStore,ite_true]
      omega

theorem readResult_scratch (extra : Nat) (w : Fin 5 ↪ Fin (extra+5))
    (store : Fin (extra+5) → List Bool) : readResult extra w store (w 3)=[] := by
  apply flagged_result_scratch
  all_goals intro eq; have := w.injective eq; contradiction

theorem readResult_counter (extra : Nat) (w : Fin 5 ↪ Fin (extra+5))
    (store : Fin (extra+5) → List Bool) : readResult extra w store (w 1)=[] := by
  unfold readResult flaggedResult
  cases Encoding.unframe (seekStore extra w store (w 0)) with
  | none => simp [parserStore,seekStore,w.injective.eq_iff]
  | some pair => obtain ⟨payload,suffix⟩:=pair; simp [parserStore,seekStore,w.injective.eq_iff]

theorem readResult_other (extra : Nat) (w : Fin 5 ↪ Fin (extra+5))
    (store : Fin (extra+5) → List Bool) (r : Fin (extra+5))
    (outside : ∀ i : Fin 5,r≠w i) : readResult extra w store r=store r := by
  unfold readResult flaggedResult
  cases Encoding.unframe (seekStore extra w store (w 0)) with
  | none => simp [parserStore,seekStore,outside]
  | some pair => obtain ⟨payload,suffix⟩:=pair; simp [parserStore,seekStore,outside]

end Counting.StackMachine.FieldAccess
