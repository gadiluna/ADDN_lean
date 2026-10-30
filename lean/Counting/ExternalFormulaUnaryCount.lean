import Counting.ExternalFormulaWitnessCount

namespace Counting.External.CookLevin.StackGenerator
open InitialRows FiniteConstraints Tableau

theorem sum_conditional {α : Type} (values : List α) (predicate : α → Bool) (yes no : Nat) :
    (values.map (fun value => if predicate value then yes else no)).sum =
      (values.filter predicate).length*yes+(values.filter (fun value => !predicate value)).length*no := by
  induction values with
  | nil => simp
  | cons value rest ih =>
    cases condition : predicate value <;> simp [condition,ih,Nat.add_mul] <;> omega

theorem initialUnary_constraint_length {time width : Nat} (setup : Setup width)
    (program : Machine.Program) (place : Fin width) :
    (initialConstraint (T := time) (setup.unary program place)).toCNF.length =
      if initialKind place.val setup.offset.val setup.header setup.capacity = .witness then
        Cellular.alphabet program-3 else Cellular.alphabet program-1 := by
  let kind := initialKind place.val setup.offset.val setup.header setup.capacity
  let head := decide (place.val=setup.offset.val)
  have template := initialUnaryTemplate_length program head kind
  have predicate : (fun tuple : Fin 1 → Fin (Cellular.alphabet program) =>
      !(initialConstraint (T := time) (setup.unary program place)).allowed tuple) =
      (fun tuple => !initialAllowed program head kind (tuple 0)) := by
    funext tuple
    rw [initialAllowed_eq]
    rfl
  simp only [initialConstraint,Setup.unary] at predicate
  simp only [Constraint.toCNF,initialConstraint,Setup.unary,List.length_map]
  rw [predicate]
  simp only [unaryTemplate,List.length_map] at template
  rw [template]
  change Cellular.alphabet program-kind.allowedCount = if kind=.witness then _ else _
  cases kind <;> rfl

/-- A positive sum form suitable for a counter implementation: each witness
cell excludes a-3 symbols, every other cell excludes a-1. -/
theorem initialUnary_block_length {time width : Nat} (setup : Setup width) (program : Machine.Program) :
    ((List.finRange width).flatMap (fun place =>
      (initialConstraint (T := time) (setup.unary program place)).toCNF)).length =
      setup.capacity*(Cellular.alphabet program-3)+
        (width-setup.capacity)*(Cellular.alphabet program-1) := by
  rw [List.length_flatMap]
  simp only [initialUnary_constraint_length]
  have counted := sum_conditional (List.finRange width)
    (fun place => decide (initialKind place.val setup.offset.val setup.header setup.capacity = .witness))
    (Cellular.alphabet program-3) (Cellular.alphabet program-1)
  simp only [decide_eq_true_eq] at counted
  rw [counted]
  have witness := initialKind_witness_count setup
  rw [witness]
  have split := List.length_eq_length_filter_add
    (l := List.finRange width)
    (fun place => decide (initialKind place.val setup.offset.val setup.header setup.capacity = .witness))
  rw [List.length_finRange,witness] at split
  congr 1
  congr 1
  omega

theorem initialUnary_block_length_sub {time width : Nat} (setup : Setup width) (program : Machine.Program) :
    ((List.finRange width).flatMap (fun place =>
      (initialConstraint (T := time) (setup.unary program place)).toCNF)).length =
      width*(Cellular.alphabet program-1)-2*setup.capacity := by
  rw [initialUnary_block_length]
  have capacityBound : setup.capacity ≤ width := by have := setup.fits; omega
  have alphabetBound : 3 ≤ Cellular.alphabet program := by unfold Cellular.alphabet; omega
  have dimensions : width-setup.capacity+setup.capacity=width := Nat.sub_add_cancel capacityBound
  have alphabetSplit : Cellular.alphabet program-3+2=Cellular.alphabet program-1 := by omega
  have balanced : setup.capacity*(Cellular.alphabet program-3)+
      (width-setup.capacity)*(Cellular.alphabet program-1)+2*setup.capacity =
      width*(Cellular.alphabet program-1) := by
    calc
      _ = (width-setup.capacity+setup.capacity)*(Cellular.alphabet program-1) := by
        rw [← alphabetSplit]
        ring
      _ = _ := by rw [dimensions]
  omega

end Counting.External.CookLevin.StackGenerator
