import Counting.StackEmitClause
import Counting.StackCompilerComplete

namespace Counting.StackMachine.Routine

/-- Standalone natural emitter: arbitrary input bits are a unary length
counter, and register one receives the canonical natural codec. -/
theorem emitNatural_computes : ComputesIn (emitNatural 0 (Function.Embedding.refl _)).program
    (fun input => Encoding.natural.encode input.length) (Complexity.polynomial 20 2) := by
  intro input
  let store : Fin 5 → List Bool := fun register => if register=0 then input else []
  obtain ⟨time,bounded,finish,ran,halted,result⟩ := emitNatural_executes 0 (Function.Embedding.refl _) store
    (by rfl) (by rfl) (by rfl)
  refine ⟨time,finish,bounded,⟨ran,halted⟩,?_⟩
  rw [result]
  change Encoding.natural.encode input.length++[]=Encoding.natural.encode input.length
  exact List.append_nil _

theorem emitClause_computes (literals : List (Nat × Bool)) :
    ComputesIn (emitClause 0 (Function.Embedding.refl _) literals).program
      (fun input => (Encoding.list literalCodec).encode (shiftedLiterals input.length literals))
      (Complexity.polynomial (clauseCoefficient literals) 2) := by
  intro input
  let store : Fin 5 → List Bool := fun register => if register=0 then input else []
  obtain ⟨time,bounded,finish,ran,halted,result⟩ := emitClause_executes 0 (Function.Embedding.refl _) literals store
    (by rfl) (by rfl) (by rfl)
  refine ⟨time,finish,bounded,⟨ran,halted⟩,?_⟩
  rw [result]
  change (Encoding.list literalCodec).encode (shiftedLiterals input.length literals)++[]=_
  exact List.append_nil _

/-- Physical five-symbol Turing machine bound, including initialization and
whole-tape cleanup, for all input words. -/
theorem emitNatural_computesCleanIn :
    Complexity.ComputesCleanIn (Compiler.compile (emitNatural 0 (Function.Embedding.refl _)).program)
      (fun input => Encoding.natural.encode input.length) (Complexity.polynomial (20*28^2) 6) :=
  Compiler.computesCleanIn_polynomial 20 2 emitNatural_computes

theorem emitClause_computesCleanIn (literals : List (Nat × Bool)) :
    Complexity.ComputesCleanIn (Compiler.compile (emitClause 0 (Function.Embedding.refl _) literals).program)
      (fun input => (Encoding.list literalCodec).encode (shiftedLiterals input.length literals))
      (Complexity.polynomial (20*(clauseCoefficient literals+8)^2) 6) :=
  Compiler.computesCleanIn_polynomial (clauseCoefficient literals) 2 (emitClause_computes literals)

end Counting.StackMachine.Routine
