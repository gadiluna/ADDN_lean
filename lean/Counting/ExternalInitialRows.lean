import Counting.ExternalWitnessWord

namespace Counting.External.InitialRows
open Machine FiniteConstraints Cellular

structure Setup (width : ℕ) where
  offset : Fin width
  header : List Bool
  capacity : ℕ
  fits : offset.val + header.length + capacity ≤ width

def Setup.witnessIndex {width : ℕ} (setup : Setup width) (position : Fin setup.capacity) : Fin width :=
  ⟨setup.offset.val + setup.header.length + position.val, by have := setup.fits; omega⟩

def Setup.symbolAllowed {width : ℕ} (setup : Setup width) (place : Fin width) (symbol : Symbol) : Prop :=
  if place.val < setup.offset.val then symbol = .blank
  else if place.val < setup.offset.val+setup.header.length then
    symbol = WitnessWord.read setup.header (place.val-setup.offset.val)
  else if place.val < setup.offset.val+setup.header.length+setup.capacity then WitnessWord.permitted symbol
  else symbol = .blank

instance {width : ℕ} (setup : Setup width) (place : Fin width) (symbol : Symbol) :
    Decidable (setup.symbolAllowed place symbol) := by unfold Setup.symbolAllowed; infer_instance

def Setup.expectedControl {width : ℕ} (setup : Setup width) (program : Program) (place : Fin width) :
    Option (Control program) := if place = setup.offset then some 0 else none

def Setup.unary {width : ℕ} (setup : Setup width) (program : Program) (place : Fin width) :
    Constraint width (alphabet program) where
  arity := 1
  position := fun _ => place
  allowed tuple :=
    let cell := (cellEquiv program).symm (tuple 0)
    decide (cell.2 = setup.expectedControl program place ∧ setup.symbolAllowed place cell.1)

def Setup.binary {width : ℕ} (setup : Setup width) (program : Program)
    (first second : Fin setup.capacity) : Constraint width (alphabet program) where
  arity := 2
  position := ![setup.witnessIndex first, setup.witnessIndex second]
  allowed tuple := decide (((cellEquiv program).symm (tuple 0)).1 = .blank →
    ((cellEquiv program).symm (tuple 1)).1 = .blank)

def Setup.constraints {width : ℕ} (setup : Setup width) (program : Program) :
    List (Constraint width (alphabet program)) :=
  (List.finRange width).map (setup.unary program) ++
    (List.finRange setup.capacity).flatMap (fun first =>
      ((List.finRange setup.capacity).filter (fun second => first.val+1 = second.val)).map
        (setup.binary program first))

def Setup.RowAllowed {width : ℕ} (setup : Setup width) (program : Program)
    (values : Fin width → Fin (alphabet program)) : Prop :=
  (∀ place, ((cellEquiv program).symm (values place)).2 = setup.expectedControl program place ∧
    setup.symbolAllowed place ((cellEquiv program).symm (values place)).1) ∧
  (∀ first second : Fin setup.capacity, first.val+1 = second.val →
    ((cellEquiv program).symm (values (setup.witnessIndex first))).1 = .blank →
    ((cellEquiv program).symm (values (setup.witnessIndex second))).1 = .blank)

theorem Setup.constraints_iff {width : ℕ} (setup : Setup width) (program : Program)
    (values : Fin width → Fin (alphabet program)) :
    (∀ constraint ∈ setup.constraints program, constraint.Satisfied values) ↔ setup.RowAllowed program values := by
  simp only [Setup.constraints, List.forall_mem_append, List.forall_mem_map, List.forall_mem_flatMap]
  simp [Setup.unary, Setup.binary, Constraint.Satisfied, Setup.RowAllowed, Function.comp_def,
    imp_iff_not_or]

def Setup.configuration {width : ℕ} (setup : Setup width) (program : Program) (witness : List Bool) :
    Cellular.Config program (Fin width) where
  control := 0
  position := setup.offset
  tape place := if place.val < setup.offset.val then .blank
    else WitnessWord.read (setup.header++witness) (place.val-setup.offset.val)

theorem Setup.witness_symbol_permitted {width : ℕ} (setup : Setup width) (program : Program)
    (values : Fin width → Fin (alphabet program)) (allowed : setup.RowAllowed program values)
    (position : Fin setup.capacity) :
    WitnessWord.permitted ((cellEquiv program).symm (values (setup.witnessIndex position))).1 := by
  have member := (allowed.1 (setup.witnessIndex position)).2
  have offsetBound : setup.offset.val ≤ (setup.witnessIndex position).val := by
    dsimp [Setup.witnessIndex]; omega
  have prefixBound : setup.offset.val+setup.header.length ≤ (setup.witnessIndex position).val := by
    dsimp [Setup.witnessIndex]; omega
  have endBound : (setup.witnessIndex position).val < setup.offset.val+setup.header.length+setup.capacity := by
    dsimp [Setup.witnessIndex]; omega
  simpa only [Setup.symbolAllowed, Nat.not_lt.mpr offsetBound, if_false,
    Nat.not_lt.mpr prefixBound, endBound, if_true] using member

theorem Setup.configuration_witness {width : ℕ} (setup : Setup width) (program : Program)
    (witness : List Bool) (position : Fin setup.capacity) :
    (setup.configuration program witness).tape (setup.witnessIndex position) = WitnessWord.read witness position.val := by
  have offsetBound : ¬(setup.witnessIndex position).val < setup.offset.val := by
    dsimp [Setup.witnessIndex]; omega
  have difference : (setup.witnessIndex position).val-setup.offset.val = setup.header.length+position.val := by
    dsimp [Setup.witnessIndex]; omega
  simp only [Setup.configuration, offsetBound, if_false, difference, WitnessWord.read_append,
    Nat.not_lt.mpr (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

theorem Setup.rowAllowed_exists {width : ℕ} (setup : Setup width) (program : Program)
    (values : Fin width → Fin (alphabet program)) (allowed : setup.RowAllowed program values) :
    ∃ witness : List Bool, witness.length ≤ setup.capacity ∧
      values = (setup.configuration program witness).encoded := by
  obtain ⟨witness, bounded, represented⟩ := WitnessWord.exists_word setup.capacity
    (fun position => ((cellEquiv program).symm (values (setup.witnessIndex position))).1)
    (setup.witness_symbol_permitted program values allowed) allowed.2
  refine ⟨witness, bounded, ?_⟩
  funext place
  apply (cellEquiv program).symm.injective
  simp only [Cellular.Config.encoded, Equiv.symm_apply_apply, Cellular.Config.cells]
  apply Prod.ext
  · have symbol := (allowed.1 place).2
    simp only [Setup.symbolAllowed] at symbol
    change ((cellEquiv program).symm (values place)).1 =
      if place.val < setup.offset.val then .blank
      else WitnessWord.read (setup.header++witness) (place.val-setup.offset.val)
    by_cases before : place.val < setup.offset.val
    · simpa only [before, if_true] using symbol
    · simp only [before, if_false] at symbol ⊢
      rw [WitnessWord.read_append]
      by_cases header : place.val < setup.offset.val+setup.header.length
      · have inPrefix : place.val-setup.offset.val < setup.header.length := by omega
        simpa only [header, inPrefix, if_true] using symbol
      · have afterPrefix : ¬place.val-setup.offset.val < setup.header.length := by omega
        simp only [header, afterPrefix, if_false] at symbol ⊢
        by_cases inside : place.val < setup.offset.val+setup.header.length+setup.capacity
        · let position : Fin setup.capacity := ⟨place.val-setup.offset.val-setup.header.length, by omega⟩
          have same : setup.witnessIndex position = place := by
            apply Fin.ext
            dsimp [Setup.witnessIndex, position]
            omega
          simpa only [same] using represented position
        · simp only [inside, if_false] at symbol
          rw [symbol, (WitnessWord.read_blank_iff witness _).mpr (by omega)]
  · exact (allowed.1 place).1

theorem Setup.configuration_allowed {width : ℕ} (setup : Setup width) (program : Program)
    (witness : List Bool) (bounded : witness.length ≤ setup.capacity) :
    setup.RowAllowed program (setup.configuration program witness).encoded := by
  simp only [Setup.RowAllowed, Cellular.Config.encoded, Equiv.symm_apply_apply, Cellular.Config.cells]
  constructor
  · intro place
    refine ⟨rfl, ?_⟩
    change setup.symbolAllowed place (if place.val < setup.offset.val then .blank
      else WitnessWord.read (setup.header++witness) (place.val-setup.offset.val))
    unfold Setup.symbolAllowed
    by_cases before : place.val < setup.offset.val
    · simp [before]
    · simp only [before, if_false, WitnessWord.read_append]
      by_cases header : place.val < setup.offset.val+setup.header.length
      · have inPrefix : place.val-setup.offset.val < setup.header.length := by omega
        simp [header, inPrefix]
      · have afterPrefix : ¬place.val-setup.offset.val < setup.header.length := by omega
        simp only [header, afterPrefix, if_false]
        split
        · exact WitnessWord.read_permitted witness _
        · exact (WitnessWord.read_blank_iff witness _).mpr (by omega)
  · intro first second adjacent blank
    rw [Setup.configuration_witness] at blank ⊢
    exact WitnessWord.read_blank_forward witness first.val second.val (by omega) blank

theorem Setup.constraints_exists_iff {width : ℕ} (setup : Setup width) (program : Program)
    (values : Fin width → Fin (alphabet program)) :
    (∀ constraint ∈ setup.constraints program, constraint.Satisfied values) ↔
      ∃ witness : List Bool, witness.length ≤ setup.capacity ∧
        values = (setup.configuration program witness).encoded := by
  rw [Setup.constraints_iff]
  constructor
  · exact setup.rowAllowed_exists program values
  · rintro ⟨witness, bounded, rfl⟩
    exact setup.configuration_allowed program witness bounded

end Counting.External.InitialRows
