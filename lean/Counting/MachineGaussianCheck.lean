import Counting.StackGaussianCheckComplete
import Counting.StackCompilerComplete

namespace Counting.Machine
open StackMachine.GaussianCheck GaussianEquationCheck GaussianNormalMatrix

def gaussianCheckProgram : Program := StackMachine.Compiler.compile complete.program

theorem gaussianCheck_clean (rows : List (List Rat)) (solution : List Rat)
    (same : ∀ row∈rows,row.length=solution.length) :
    ∃ time output,
      time≤ 20*(1000000000000046)^2*((inputCodec.encode (solution,rows)).length+1)^10 ∧
      HaltsAt gaussianCheckProgram (inputCodec.encode (solution,rows)) time output ∧
      output.tape.denotes=Turing.Tape.mk₁ ([accepts rows solution].map bitSymbol) := by
  obtain ⟨steps,last,bounded,halted,stored⟩ := complete_halts rows solution same
  obtain ⟨time,output,timeBound,executed,tape⟩ := StackMachine.Compiler.compile_halts halted
  refine ⟨time,output,timeBound.trans ?_,executed,?_⟩
  · let size := (inputCodec.encode (solution,rows)).length
    change 20*(size+41+steps+4)^2≤ 20*(1000000000000046)^2*(size+1)^10
    have linear := Nat.le_self_pow (by decide:5≠0) (size+1)
    have positive := Nat.one_le_pow' 5 size
    change steps≤ 1000000000000000*(size+1)^5 at bounded
    have base : size+41+steps+4≤ 1000000000000046*(size+1)^5 := by omega
    calc
      _≤ 20*(1000000000000046*(size+1)^5)^2 := Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left base 2)
      _=_ := by ring
  · rw [stored] at tape
    exact tape

/-- The checked Boolean is precisely the original equation test in
`Executable.solveLinear?`, after adjoining the physically represented
last coefficient -1 to the supplied solution vector. -/
theorem gaussianCheck_original_clean (width : Nat) (rows : List Executable.Equation)
    (solution : Fin width → Rat) :
    ∃ time output,
      time≤ 20*(1000000000000046)^2*
        ((inputCodec.encode (vector (List.ofFn solution),equationMatrix width rows)).length+1)^10 ∧
      HaltsAt gaussianCheckProgram
        (inputCodec.encode (vector (List.ofFn solution),equationMatrix width rows)) time output ∧
      output.tape.denotes=Turing.Tape.mk₁
        ([rows.all (fun row =>
          ((List.finRange width).map (fun i => (row.1[i.val]?.getD 0)*solution i)).sum == row.2)].map bitSymbol) := by
  have same : ∀ row∈equationMatrix width rows,row.length=(vector (List.ofFn solution)).length := by
    intro row member
    obtain ⟨equation,_,rfl⟩ := List.mem_map.mp member
    simp
  obtain ⟨time,output,bounded,halted,tape⟩ :=
    gaussianCheck_clean (equationMatrix width rows) (vector (List.ofFn solution)) same
  rw [accepts_original] at tape
  exact ⟨time,output,bounded,halted,tape⟩

end Counting.Machine
