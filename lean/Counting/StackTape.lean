import Counting.StackMachine
import Counting.MachineTapeBounds
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.FinRange

namespace Counting.StackMachine
open Machine

def stores {registers : ℕ} (store : Fin registers → List Bool) : List (List Bool) :=
  (List.finRange registers).map store

def before {registers : ℕ} (store : Fin registers → List Bool) (register : Fin registers) : List Symbol :=
  ((stores store).take register.val).flatMap block

def after {registers : ℕ} (store : Fin registers → List Bool) (register : Fin registers) : List Symbol :=
  ((stores store).drop (register.val+1)).flatMap block

theorem stores_length {registers : ℕ} (store : Fin registers → List Bool) :
    (stores store).length = registers := by simp [stores]

theorem stores_get {registers : ℕ} (store : Fin registers → List Bool) (register : Fin registers) :
    (stores store)[register.val]'(by rw [stores_length]; exact register.isLt) = store register := by
  simp [stores]

theorem stores_split {registers : ℕ} (store : Fin registers → List Bool) (register : Fin registers) :
    stores store = (stores store).take register.val ++ store register :: (stores store).drop (register.val+1) := by
  rw [← stores_get store register, List.getElem_cons_drop,
    List.take_append_drop]

theorem stores_update {registers : ℕ} (store : Fin registers → List Bool) (register : Fin registers)
    (value : List Bool) : stores (Function.update store register value) =
      (stores store).take register.val ++ value :: (stores store).drop (register.val+1) := by
  unfold stores
  rw [(List.nodup_finRange registers).map_update, if_pos (by simp), List.idxOf_finRange,
    List.set_eq_take_append_cons_drop, if_pos (by simp)]

theorem encoded_eq_blocks {program : Program} (config : Config program) :
    config.encoded = .mark :: (stores config.store).flatMap block := by
  simp only [Config.encoded, stores, List.flatMap_map]

theorem encoded_split {program : Program} (config : Config program) (register : Register program) :
    config.encoded = .mark :: (before config.store register ++ block (config.store register) ++ after config.store register) := by
  rw [encoded_eq_blocks, stores_split config.store register]
  simp only [List.flatMap_append, List.flatMap_cons, before, after, List.append_assoc]

theorem encoded_update {program : Program} (config : Config program) (register : Register program)
    (value : List Bool) (control : Control program) :
    (⟨control, Function.update config.store register value⟩ : Config program).encoded =
      .mark :: (before config.store register ++ block value ++ after config.store register) := by
  rw [encoded_eq_blocks, stores_update]
  simp only [List.flatMap_append, List.flatMap_cons, before, after, List.append_assoc]

theorem blocks_ne_mark (values : List (List Bool)) :
    ∀ symbol ∈ values.flatMap block, symbol ≠ .mark := by
  intro symbol member
  obtain ⟨bits, _, present⟩ := List.mem_flatMap.mp member
  exact block_ne_mark bits symbol present

theorem blocks_ne_blank (values : List (List Bool)) :
    ∀ symbol ∈ values.flatMap block, symbol ≠ .blank := by
  intro symbol member
  obtain ⟨bits, _, present⟩ := List.mem_flatMap.mp member
  exact block_ne_blank bits symbol present

theorem split_length_bound {program : Program} (config : Config program) (register : Register program) :
    (before config.store register).length + (block (config.store register)).length +
      (after config.store register).length+1 = config.encoded.length := by
  rw [encoded_split config register]
  simp only [List.length_cons, List.length_append]

end Counting.StackMachine
