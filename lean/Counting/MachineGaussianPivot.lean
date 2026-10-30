import Counting.StackGaussianPivot
import Counting.StackCompilerComplete

namespace Counting.Machine
open DirectedCounting.VerifiedGaussianAnchorSolver RationalSystem
open StackMachine.GaussianPivot

def gaussianPivotProgram : Program := StackMachine.Compiler.compile complete.program

/-- A concrete single-tape machine selects exactly the pivot used by
StoredGaussian. It reads and traverses the serialized matrix, and returns
its optional row index in binary on a completely clean tape. The explicit
unary diagonal input is bounded by the number of represented rows. -/
theorem gaussianPivot_clean {q : Nat} (system : RationalSystem q) (pivot : Fin q) :
    ∃ time output,
      time  ≤  (20*50040^2)*((inputWord (StoredGaussian.augmentedMatrix system) pivot.val).length+1)^6 ∧
      HaltsAt gaussianPivotProgram (inputWord (StoredGaussian.augmentedMatrix system) pivot.val) time output ∧
      output.tape.denotes=Turing.Tape.mk₁
        ((Encoding.optionalNatural.encode ((findPivot? system pivot).map Fin.val)).map bitSymbol) := by
  obtain ⟨steps,last,bounded,halted,stored⟩ := complete_halts system pivot
  obtain ⟨time,output,timeBound,executed,tape⟩ := StackMachine.Compiler.compile_halts halted
  refine ⟨time,output,timeBound.trans ?_,executed,?_⟩
  · let size := (inputWord (StoredGaussian.augmentedMatrix system) pivot.val).length
    change 20*(size+29+steps+4)^2 ≤ (20*50040^2)*(size+1)^6
    have linear := Nat.le_self_pow (by decide : 3≠0) (size+1)
    have positive := Nat.one_le_pow' 3 size
    have base : size+29+steps+4 ≤ 50040*(size+1)^3 := by
      change steps ≤ 50000*(size+1)^3 at bounded
      omega
    calc
      _  ≤ 20*(50040*(size+1)^3)^2 := Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left base 2)
      _ = _ := by ring
  · rw [stored] at tape
    exact tape

end Counting.Machine
