import Counting.StackDagSortComplete
import Counting.StackCompilerComplete

namespace Counting.Machine
open StackMachine.DagUpdate.Sort

def dagSortProgram : Program := StackMachine.Compiler.compile completeSort.program

/-- The concrete finite-control machine sorts compact indexed signatures.
Its entire output tape contains only the framed result. No count, node,
or comparison primitive is charged as a unit-cost oracle. -/
theorem dagSort_clean (records : List Record) :
    ∃time output,
      time≤20*(30000+99)^2*((sortInput records).length+1)^10 ∧
      HaltsAt dagSortProgram (sortInput records) time output ∧
      output.tape.denotes=Turing.Tape.mk₁ ((sortOutput records).map bitSymbol) := by
  obtain ⟨steps,bounded,last,ran,halted,stored⟩:=completeSort_executes records
  have stackHalt:StackMachine.HaltsAt completeSort.program (sortInput records) steps last:=⟨ran,halted⟩
  obtain ⟨time,output,timeBound,execution,tape⟩:=StackMachine.Compiler.compile_halts stackHalt
  refine ⟨time,output,timeBound.trans ?_,execution,?_⟩
  · let N:=(sortInput records).length
    have linear:N+1≤(N+1)^5:=Nat.le_self_pow (by decide) _
    have positive:1≤(N+1)^5:=Nat.one_le_pow' 5 N
    have base:N+94+steps+4≤(30000+99)*(N+1)^5:=by
      change steps≤30000*(N+1)^5 at bounded
      omega
    calc
      _≤20*((30000+99)*(N+1)^5)^2:=Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left base 2)
      _=_:=by dsimp [N];ring
  · rw [stored] at tape
    exact tape

/-- Supplying the level collector's reversed stream gives exactly the
stable indexed signature order used by `Executable.canonicalize`. -/
theorem dagSort_canonical_order (source : Executable.Vista) (mapping : Array Nat) (indices : List Nat) :
    ∃time output,
      time≤20*(30000+99)^2*((sortInput (indexedSignatures source mapping indices).reverse).length+1)^10 ∧
      HaltsAt dagSortProgram (sortInput (indexedSignatures source mapping indices).reverse) time output ∧
      output.tape.denotes=Turing.Tape.mk₁
        (((Encoding.list recordCodec).encode (indexedSignatures source mapping
          (indices.mergeSort (fun i j=>Executable.lexLE
            (Executable.referenceMap mapping (source.node i)).key
            (Executable.referenceMap mapping (source.node j)).key)))).map bitSymbol) := by
  simpa only [completeSort_indexed] using dagSort_clean (indexedSignatures source mapping indices).reverse

end Counting.Machine
