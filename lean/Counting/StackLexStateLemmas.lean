import Counting.StackLexState

namespace Counting.StackMachine.Lexicographic

namespace LexState

theorem advance_valid (value : LexState) (valid : value.Valid) : value.advance.Valid := by
  rcases value with ⟨left,right,unresolved,answer⟩
  cases left with
  | nil => exact valid
  | cons a left =>
    cases right with
    | nil => simp [advance,Valid]
    | cons b right =>
      cases unresolved <;> simp_all [advance,Valid]

theorem advance_finalValue (value : LexState) : value.advance.finalValue=value.finalValue := by
  rcases value with ⟨left,right,unresolved,answer⟩
  cases left with
  | nil => rfl
  | cons a left =>
    cases right with
    | nil => cases unresolved <;> rfl
    | cons b right =>
      by_cases equal : a=b
      · subst b
        cases unresolved <;> simp [advance,finalValue,Executable.lexLE]
      · have order : decide (a≤b)=decide (a<b) := by
          apply Bool.eq_iff_iff.mpr
          simp only [decide_eq_true_eq]
          omega
        cases unresolved <;> simp [advance,finalValue,Executable.lexLE,equal,order]

theorem advance_left_length (value : LexState) : value.advance.left.length≤value.left.length-1 := by
  rcases value with ⟨left,right,unresolved,answer⟩
  cases left <;> cases right <;> simp [advance]

theorem advance_encodedLength (value : LexState) : value.advance.encodedLength≤value.encodedLength := by
  rcases value with ⟨left,right,unresolved,answer⟩
  cases left <;> cases right <;> simp [advance,encodedLength,Encoding.sequence,List.length_append]
  omega

theorem iterate_valid (value : LexState) (valid : value.Valid) (count : Nat) :
    ((advance)^[count] value).Valid := by
  induction count with
  | zero => exact valid
  | succ count ih =>
    rw [Function.iterate_succ_apply']
    exact advance_valid _ ih

theorem iterate_finalValue (value : LexState) (count : Nat) :
    ((advance)^[count] value).finalValue=value.finalValue := by
  induction count with
  | zero => rfl
  | succ count ih => rw [Function.iterate_succ_apply',advance_finalValue,ih]

theorem iterate_left_length (value : LexState) (count : Nat) :
    ((advance)^[count] value).left.length≤value.left.length-count := by
  induction count with
  | zero => simp
  | succ count ih =>
    rw [Function.iterate_succ_apply']
    have next := advance_left_length ((advance)^[count] value)
    omega

theorem iterate_encodedLength (value : LexState) (count : Nat) :
    ((advance)^[count] value).encodedLength≤value.encodedLength := by
  induction count with
  | zero => exact le_rfl
  | succ count ih =>
    rw [Function.iterate_succ_apply']
    exact (advance_encodedLength _).trans ih

theorem finalValue_of_left_nil (value : LexState) (valid : value.Valid) (empty : value.left=[]) :
    value.finalValue=value.answer := by
  unfold finalValue
  cases h : value.unresolved with
  | false => rfl
  | true => simp [empty,Executable.lexLE,valid h]

theorem iterate_answer (value : LexState) (valid : value.Valid) (count : Nat) (enough : value.left.length≤count) :
    ((advance)^[count] value).left=[] ∧ ((advance)^[count] value).answer=value.finalValue := by
  have bound := iterate_left_length value count
  have empty : ((advance)^[count] value).left=[] := List.length_eq_zero_iff.mp (by omega)
  refine ⟨empty,?_⟩
  rw [←finalValue_of_left_nil _ (iterate_valid value valid count) empty,iterate_finalValue]

end LexState
end Counting.StackMachine.Lexicographic
