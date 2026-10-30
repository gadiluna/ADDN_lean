import Counting.StackGaussianNormalInput
import Counting.GaussianAnchorDomain

namespace Counting.GaussianLinearInputSize
open Executable GaussianNormalMatrix

private theorem framed_sequence_bound {α:Type} (codec : Encoding.Codec α) (values : List α) (bound : Nat)
    (bounded : ∀ value∈values,(codec.encode value).length≤ bound) :
    (Encoding.sequence (Encoding.framed codec) values).length≤ values.length*(2*bound+1) := by
  induction values with
  | nil => simp [Encoding.sequence]
  | cons value rest ih =>
    have head := bounded value (by simp)
    have tailBound := ih (by intro x member;exact bounded x (List.mem_cons_of_mem value member))
    simp only [Encoding.sequence,List.length_append,Encoding.framed_length,List.length_cons]
    nlinarith

def rowBound (width bits : Nat) : Nat := 2*(width+1)+1+(width+1)*(4*bits+7)
def inputBound (width count bits : Nat) : Nat := 2*width+1+(2*count+1)+count*(2*rowBound width bits+1)

theorem row_length_bound (values : List Rat) (bits : Nat)
    (bounded : ∀ value∈values,value.num.natAbs.size+value.den.size≤ bits) :
    (Encoding.rationalRow.encode values).length≤ 2*values.length+1+values.length*(4*bits+7) := by
  have sequenceBound := framed_sequence_bound Encoding.rational values (2*bits+3) (by
    intro value member;rw [Encoding.rational_length];have current:=bounded value member;omega)
  rw [show 2*(2*bits+3)+1=4*bits+7 by omega] at sequenceBound
  have sizeBound : values.length.size≤ values.length := Nat.size_le.mpr Nat.lt_two_pow_self
  change (Encoding.natural.encode values.length++_).length≤ _
  rw [List.length_append,Encoding.natural_length]
  omega

/-- This is a length bound on the exact internal tape supplied to the
solver, including unary width, all row frames, binary list headers and
both numerator and denominator fields. -/
theorem input_length_bound (width : Nat) (rows : List Equation) (sized : RowsSized width rows)
    (bits : Nat) (bounded : ∀ row∈rows,∀ value∈row.1.toList++[row.2],
      value.num.natAbs.size+value.den.size≤ bits) :
    (StackMachine.GaussianNormal.inputWord width (equationMatrix width rows)).length≤ inputBound width rows.length bits := by
  have rowBounds : ∀ row∈equationMatrix width rows,(Encoding.rationalRow.encode row).length≤ rowBound width bits := by
    intro row member
    obtain ⟨equation,present,rfl⟩ := List.mem_map.mp member
    rw [equationRow_of_size width equation (sized equation present)]
    have bound := row_length_bound (equation.1.toList++[equation.2]) bits (bounded equation present)
    have length : (equation.1.toList++[equation.2]).length=width+1 := by simp [sized equation present]
    rw [length] at bound
    exact bound
  have stream := framed_sequence_bound Encoding.rationalRow (equationMatrix width rows) (rowBound width bits) rowBounds
  have count : rows.length.size≤ rows.length := Nat.size_le.mpr Nat.lt_two_pow_self
  change (Encoding.frame (List.replicate width true)++
    (Encoding.natural.encode (equationMatrix width rows).length++_)).length≤ _
  simp only [List.length_append,Encoding.frame_length,List.length_replicate,equationMatrix_length,Encoding.natural_length] at *
  unfold inputBound
  omega

theorem anchor_input_length (vista : Vista) (anchor leaders M : Nat)
    (degrees : ∀ i,i<vista.nodes.size→(vista.node i).degree≤ M)
    (reds : ∀ i,i<vista.nodes.size→∀ old,countFrom (vista.node i) old≤ M) :
    (StackMachine.GaussianNormal.inputWord (levelNodes vista anchor).length
      (equationMatrix (levelNodes vista anchor).length (anchorRows vista anchor leaders))).length≤ inputBound (levelNodes vista anchor).length ((levelNodes vista (anchor-1)).length+1) (M.size+leaders.size+2) := by
  have bounded : ∀ row∈anchorRows vista anchor leaders,∀ value∈row.1.toList++[row.2],
      value.num.natAbs.size+value.den.size≤ M.size+leaders.size+2 := by
    intro row member value present
    rcases List.mem_append.mp present with coeff | rhs
    · have bound := (anchorRows_coefficients vista anchor leaders M degrees reds row member value coeff).2.2
      omega
    · have equal : value=row.2 := List.mem_singleton.mp rhs
      subst value
      have bound := (anchorRows_rhs vista anchor leaders row member).2.2
      omega
  have result := input_length_bound _ _ (anchorRows_sized vista anchor leaders) _ bounded
  simpa only [anchorRows,List.length_append,List.length_map,List.length_singleton] using result

theorem inputBound_polynomial (width count bits population : Nat) (widthBound : width≤ population)
    (countBound : count≤ population+1) :
    inputBound width count bits≤ 100*(population+1)^2*(bits+1) := by
  have monotone : inputBound width count bits≤ inputBound population (population+1) bits := by
    dsimp only [inputBound,rowBound]
    gcongr
  apply monotone.trans
  dsimp only [inputBound,rowBound]
  ring_nf
  omega

end Counting.GaussianLinearInputSize
