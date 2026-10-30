import Counting.StackGaussianLinearComplete
import Counting.StackGaussianNormalBounds

namespace Counting.StackMachine.GaussianCalls
open Routine GaussianNormalMatrix GaussianBits GaussianEquationCheck
open DirectedCounting.VerifiedGaussianAnchorSolver RationalSystem
set_option maxRecDepth 20000
set_option exponentiation.threshold 4000

theorem normalWord_length_bound (width : Nat) (equations : List Executable.Equation) :
    (Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix (Executable.normalSystem width equations))).length≤ 100*((GaussianNormal.inputWord width (equationMatrix width equations)).length+1)^3 := by
  let size := (Encoding.rationalMatrix.encode (equationMatrix width equations)).length
  let length := (GaussianNormal.inputWord width (equationMatrix width equations)).length
  have inputLength : length=2*width+1+size := by
    simp [length,GaussianNormal.inputWord,Encoding.frame_length,size]
  have streamBound := GaussianNormal.normalStream_encoded_bound width equations
  have headerBound : (Encoding.natural.encode width).length≤ 2*width+1 := by
    rw [Encoding.natural_length]
    exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.size_le.mpr Nat.lt_two_pow_self)) 1
  have encoded : (Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix (Executable.normalSystem width equations))).length≤ 2*width+1+GaussianNormal.normalStreamBound width size := by
    change (Encoding.natural.encode (StoredGaussian.augmentedMatrix _).length++_).length≤ _
    rw [List.length_append,StoredGaussian.augmentedMatrix_length]
    dsimp only [size]
    omega
  have monotone : 2*width+1+GaussianNormal.normalStreamBound width size≤ 2*length+1+GaussianNormal.normalStreamBound length length := by
    dsimp only [GaussianNormal.normalStreamBound,GaussianNormal.normalRowBound]
    gcongr <;> omega
  apply encoded.trans (monotone.trans _)
  change 2*length+1+GaussianNormal.normalStreamBound length length≤ 100*(length+1)^3
  dsimp only [GaussianNormal.normalStreamBound,GaussianNormal.normalRowBound]
  ring_nf
  omega

theorem solutionWord_length_bound {q : Nat} (system : RationalSystem q)
    (integral : ∀ row column,(augmented system row column).den=1)
    (solution : Fin q → Rat) (found : StoredGaussian.solve? system=some solution) :
    (Encoding.rationalRow.encode (List.ofFn solution)).length≤ (GaussianBank.solverPolynomialCoefficient+1)*
        ((Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix system)).length+1)^100 := by
  obtain ⟨time,last,bounded,⟨ran,_⟩,stored⟩ := square_halts system integral
  have data := run_dataLength (initial GaussianBank.complete.program
    (Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix system))) last time ran
  rw [initial_dataLength] at data
  have localBound : (last.store 1).length≤ last.dataLength :=
    Finset.single_le_sum (f:=fun r=>(last.store r).length) (fun _ _=>Nat.zero_le _) (Finset.mem_univ 1)
  rw [stored,found] at localBound
  simp only [Option.map_some,Encoding.optional,List.length_cons] at localBound
  have linear := Nat.le_self_pow (by decide:100≠0)
    ((Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix system)).length+1)
  nlinarith

theorem vectorWord_length_bound (values : List Rat) :
    (Encoding.rationalRow.encode (vector values)).length≤ 3*(Encoding.rationalRow.encode values).length+18 := by
  let fields := Encoding.sequence (Encoding.framed Encoding.rational) values
  have appendFields : Encoding.sequence (Encoding.framed Encoding.rational) (values++[-1])=
      fields++Encoding.frame (Encoding.rational.encode (-1)) := by
    dsimp only [fields]
    clear fields
    induction values with
    | nil => rfl
    | cons value rest ih =>
      simpa only [List.cons_append,Encoding.sequence,List.append_assoc] using
        congrArg (fun xs=>(Encoding.framed Encoding.rational).encode value++xs) ih
  have count := Encoding.framedList_count_le Encoding.rational values
  change values.length≤ (Encoding.rationalRow.encode values).length at count
  have bits : (values.length+1).size≤ values.length+1 := Nat.size_le.mpr Nat.lt_two_pow_self
  have oldLength : (Encoding.rationalRow.encode values).length=(Encoding.natural.encode values.length).length+fields.length := List.length_append
  have lastLength : (Encoding.frame (Encoding.rational.encode (-1))).length=15 := by decide
  change (Encoding.natural.encode (vector values).length++Encoding.sequence (Encoding.framed Encoding.rational) (values++[-1])).length≤ _
  rw [vector_length,List.length_append,appendFields,List.length_append,lastLength,Encoding.natural_length]
  omega

def solutionPolynomialCoefficient : Nat := (GaussianBank.solverPolynomialCoefficient+1)*101^100

theorem linearSolution_length_bound (width : Nat) (equations : List Executable.Equation)
    (integral : ∀ row column,(augmented (Executable.normalSystem width equations) row column).den=1)
    (solution : Fin width → Rat) (found : StoredGaussian.solve? (Executable.normalSystem width equations)=some solution) :
    (Encoding.rationalRow.encode (List.ofFn solution)).length≤ solutionPolynomialCoefficient*((GaussianNormal.inputWord width (equationMatrix width equations)).length+1)^300 := by
  let length := (GaussianNormal.inputWord width (equationMatrix width equations)).length
  have normalBound := normalWord_length_bound width equations
  change (Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix (Executable.normalSystem width equations))).length≤
    100*(length+1)^3 at normalBound
  have positive := Nat.one_le_pow' 3 length
  have plus : (Encoding.rationalMatrix.encode (StoredGaussian.augmentedMatrix (Executable.normalSystem width equations))).length+1≤ 101*(length+1)^3 := by omega
  apply (solutionWord_length_bound _ integral solution found).trans
  calc
    _≤ (GaussianBank.solverPolynomialCoefficient+1)*(101*(length+1)^3)^100 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left plus 100)
    _=solutionPolynomialCoefficient*(length+1)^300 := by
      change (GaussianBank.solverPolynomialCoefficient+1)*(101*(length+1)^3)^100=
        ((GaussianBank.solverPolynomialCoefficient+1)*101^100)*(length+1)^300
      have power : ((length+1)^3)^100=(length+1)^300 := (pow_mul (length+1) 3 100).symm
      rw [mul_pow,power,Nat.mul_assoc]

end Counting.StackMachine.GaussianCalls
