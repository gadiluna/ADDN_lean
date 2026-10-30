import Counting.StackGaussianNormalOutput

namespace Counting.StackMachine.GaussianNormal
open Routine GaussianNormalMatrix

private theorem framed_sequence_bound {α : Type} (codec : Encoding.Codec α) (values : List α) (bound : Nat)
    (bounded : ∀ value∈values,(codec.encode value).length≤bound) :
    (Encoding.sequence (Encoding.framed codec) values).length≤values.length*(2*bound+1) := by
  induction values with
  | nil => simp [Encoding.sequence]
  | cons value rest ih =>
    have current := bounded value (by simp)
    have tailBound := ih (by intro x member;exact bounded x (List.mem_cons_of_mem value member))
    simp only [Encoding.sequence,List.length_append,Encoding.framed_length,List.length_cons]
    nlinarith

def normalRowBound (width size : Nat) : Nat := 2*(width+1)+1+(width+1)*(16*size+15)
def normalStreamBound (width size : Nat) : Nat := width*(2*normalRowBound width size+1)

theorem normalRow_encoded_bound (width : Nat) (equations : List Executable.Equation) (row : Fin width) :
    (Encoding.rationalRow.encode (StoredGaussian.augmentedRow (Executable.normalSystem width equations) row)).length ≤
      normalRowBound width (Encoding.rationalMatrix.encode (equationMatrix width equations)).length := by
  have fields := columnValues_fields_bound width equations row.val 0 (width+1) (by omega) (by omega)
  rw [columnValues_full width equations row] at fields
  have bits : (width+1).size≤width+1 := Nat.size_le.mpr Nat.lt_two_pow_self
  change (Encoding.natural.encode (StoredGaussian.augmentedRow (Executable.normalSystem width equations) row).length++_).length≤_
  simp only [List.length_append,StoredGaussian.augmentedRow_length,Encoding.natural_length]
  unfold normalRowBound
  omega

theorem normalStream_encoded_bound (width : Nat) (equations : List Executable.Equation) :
    (Encoding.sequence (Encoding.framed Encoding.rationalRow)
      (StoredGaussian.augmentedMatrix (Executable.normalSystem width equations))).length ≤
      normalStreamBound width (Encoding.rationalMatrix.encode (equationMatrix width equations)).length := by
  apply (framed_sequence_bound Encoding.rationalRow _
    (normalRowBound width (Encoding.rationalMatrix.encode (equationMatrix width equations)).length) ?_).trans_eq
    (by simp [normalStreamBound])
  intro row member
  change row∈List.ofFn (StoredGaussian.augmentedRow (Executable.normalSystem width equations)) at member
  obtain ⟨index,rfl⟩ := List.mem_ofFn.mp member
  exact normalRow_encoded_bound width equations index

def generatorBudget (width size : Nat) : Nat :=
  width*(rowBudget size width+2)+8*normalStreamBound width size+12*(2*width+1)+13

theorem generate_bounded (width : Nat) (equations : List Executable.Equation) :
    ∃ time ≤ generatorBudget width (Encoding.rationalMatrix.encode (equationMatrix width equations)).length,
      Executes generate (state width equations 0 0 [] (List.replicate width true) [] [] []) time
        (outputStore width equations) := by
  obtain ⟨time,bounded,ran⟩ := generate_executes width equations
  have streamBound := normalStream_encoded_bound width equations
  have headerBound : (Encoding.natural.encode width).length≤2*width+1 := by
    rw [Encoding.natural_length]
    exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.size_le.mpr Nat.lt_two_pow_self)) 1
  exact ⟨time,by dsimp [generatorBudget];omega,ran⟩

end Counting.StackMachine.GaussianNormal
