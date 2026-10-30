import Counting.Executable
import Mathlib.Data.List.Lex
import Mathlib.Data.List.Sort

namespace Counting.Executable

/-- The executable comparator is the ordinary non-strict lexicographic
order, including the empty-prefix cases. -/
theorem lexLE_true_iff_not_reverse (left right : List Nat) :
    lexLE left right=true ↔ ¬List.Lex (·<·) right left := by
  induction left generalizing right with
  | nil => simp [lexLE]
  | cons a left ih =>
    cases right with
    | nil => simp [lexLE]
    | cons b right =>
      by_cases same : a=b
      · subst b
        simpa [lexLE,List.cons_lex_cons_iff] using ih right
      · simp only [lexLE,beq_iff_eq,same,if_false,decide_eq_true_eq,
          List.cons_lex_cons_iff,Ne.symm same,false_and,or_false]
        omega

theorem lexLE_true_iff_le (left right : List Nat) :
    lexLE left right=true ↔ left≤right := by
  rw [lexLE_true_iff_not_reverse]
  change ¬right<left ↔ left≤right
  exact not_lt

theorem lexLE_refl (value : List Nat) : lexLE value value=true :=
  (lexLE_true_iff_le _ _).mpr le_rfl

theorem lexLE_trans {first second third : List Nat}
    (before : lexLE first second=true) (after : lexLE second third=true) :
    lexLE first third=true :=
  (lexLE_true_iff_le _ _).mpr (le_trans ((lexLE_true_iff_le _ _).mp before)
    ((lexLE_true_iff_le _ _).mp after))

theorem lexLE_total (first second : List Nat) : lexLE first second=true ∨ lexLE second first=true :=
  (le_total first second).imp ((lexLE_true_iff_le _ _).mpr) ((lexLE_true_iff_le _ _).mpr)

theorem lexLE_antisymm {first second : List Nat}
    (before : lexLE first second=true) (after : lexLE second first=true) : first=second :=
  le_antisymm ((lexLE_true_iff_le _ _).mp before) ((lexLE_true_iff_le _ _).mp after)

private theorem flatten_pairs_injective :
    Function.Injective (fun values : List (Nat×Nat)=>values.flatMap (fun edge=>[edge.1,edge.2])) := by
  intro first second equal
  induction first generalizing second with
  | nil =>
    cases second with
    | nil => rfl
    | cons pair rest => simp at equal
  | cons pair rest ih =>
    cases second with
    | nil => simp at equal
    | cons other tail =>
      simp only [List.flatMap_cons,List.cons_append,List.nil_append,List.cons.injEq] at equal
      have pairEqual : pair=other := Prod.ext equal.1 equal.2.1
      exact congrArg₂ List.cons pairEqual (ih equal.2.2)

private theorem parentNumber_injective :
    Function.Injective (fun parent : Option Nat=>(parent.map (·+1)).getD 0) := by
  intro first second equal
  cases first <;> cases second <;> simp_all

/-- A full signature determines every stored field, including all red
edge multiplicities in their given order. -/
theorem Node.key_injective : Function.Injective Node.key := by
  intro first second equal
  rcases first with ⟨level,parent,leader,degree,incoming⟩
  rcases second with ⟨level',parent',leader',degree',incoming'⟩
  simp only [Node.key,List.cons_append,List.nil_append,List.cons.injEq] at equal
  obtain ⟨levels,leaders,parents,degrees,edges⟩ := equal
  have parentEqual := parentNumber_injective parents
  have leaderEqual : leader=leader' := by cases leader <;> cases leader' <;> simp_all
  have edgeEqual := flatten_pairs_injective edges
  subst level'
  subst parent'
  subst leader'
  subst degree'
  subst incoming'
  rfl

theorem Node.key_antisymm {first second : Node}
    (before : lexLE first.key second.key=true) (after : lexLE second.key first.key=true) : first=second :=
  Node.key_injective (lexLE_antisymm before after)

end Counting.Executable
