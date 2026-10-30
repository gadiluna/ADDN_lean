import Counting.StackEmitOffset

namespace Counting.StackMachine.Routine

abbrev literalCodec := Encoding.product Encoding.natural Encoding.boolean

def shiftedLiterals (base : Nat) (literals : List (Nat × Bool)) : List (Nat × Bool) :=
  literals.map (fun literal => (base+literal.1,literal.2))

def emitOffsetList (extra : Nat) (w : PowerWorkspace extra) : List (Nat × Bool) → Routine (extra+3)
  | [] => skip (extra+3)
  | literal::rest => sequence (emitOffsetList extra w rest)
      (emitOffsetLiteral extra w literal.1 literal.2)

def offsetListCoefficient : List (Nat × Bool) → Nat
  | [] => 0
  | literal::rest => offsetListCoefficient rest+1+offsetLiteralCoefficient literal.1

theorem emitOffsetList_executes (extra : Nat) (w : PowerWorkspace extra) (literals : List (Nat × Bool))
    (store : Fin (extra+5) → List Bool) (counterEmpty : store (w 2) = [])
    (binaryEmpty : store (w 3) = []) (workEmpty : store (w 4) = []) :
    ∃ transitions ≤ offsetListCoefficient literals*((store (w 0)).length+1)^2,
      Executes (emitOffsetList extra w literals) store transitions
        (Function.update store (w 1)
          (Encoding.sequence literalCodec (shiftedLiterals (store (w 0)).length literals)++store (w 1))) := by
  induction literals generalizing store with
  | nil =>
      refine ⟨0,by simp [offsetListCoefficient],?_⟩
      simpa only [emitOffsetList,shiftedLiterals,List.map_nil,Encoding.sequence,List.nil_append,Function.update_eq_self] using skip_executes store
  | cons literal rest ih =>
      obtain ⟨tailTime,tailBound,tailRun⟩ := ih store counterEmpty binaryEmpty workEmpty
      let middle := Function.update store (w 1)
        (Encoding.sequence literalCodec (shiftedLiterals (store (w 0)).length rest)++store (w 1))
      obtain ⟨headTime,headBound,headRun⟩ := emitOffsetLiteral_executes extra w literal.1 literal.2 middle
        (by simp [middle,w.injective.eq_iff,counterEmpty])
        (by simp [middle,w.injective.eq_iff,binaryEmpty])
        (by simp [middle,w.injective.eq_iff,workEmpty])
      have combined := tailRun.sequence headRun
      refine ⟨tailTime+1+headTime,?_,?_⟩
      · simp only [middle,Function.update_of_ne (workspace_ne w (by decide : (0 : Fin 5) ≠ 1))] at headBound
        have positive : 1 ≤ ((store (w 0)).length+1)^2 := Nat.one_le_pow 2 _ (by omega)
        unfold offsetListCoefficient
        nlinarith
      · simpa only [emitOffsetList,middle,Function.update_self,Function.update_idem,
          Function.update_of_ne (workspace_ne w (by decide : (0 : Fin 5) ≠ 1)),shiftedLiterals,
          List.map_cons,Encoding.sequence,List.append_assoc] using combined

/-- The literal pattern is part of the fixed machine code. Its identifiers
are offsets from a runtime unary base, and the clause length is encoded. -/
def emitClause (extra : Nat) (w : PowerWorkspace extra) (literals : List (Nat × Bool)) : Routine (extra+3) :=
  sequence (emitOffsetList extra w literals) (prepend (w 1) (Encoding.natural.encode literals.length))

def clauseCoefficient (literals : List (Nat × Bool)) : Nat :=
  offsetListCoefficient literals+1+2*(Encoding.natural.encode literals.length).length

theorem emitClause_executes (extra : Nat) (w : PowerWorkspace extra) (literals : List (Nat × Bool))
    (store : Fin (extra+5) → List Bool) (counterEmpty : store (w 2) = [])
    (binaryEmpty : store (w 3) = []) (workEmpty : store (w 4) = []) :
    ∃ transitions ≤ clauseCoefficient literals*((store (w 0)).length+1)^2,
      Executes (emitClause extra w literals) store transitions
        (Function.update store (w 1)
          ((Encoding.list literalCodec).encode (shiftedLiterals (store (w 0)).length literals)++store (w 1))) := by
  obtain ⟨bodyTime,bodyBound,bodyRun⟩ := emitOffsetList_executes extra w literals store counterEmpty binaryEmpty workEmpty
  have header := prepend_executes (w 1) (Encoding.natural.encode literals.length)
    (Function.update store (w 1)
      (Encoding.sequence literalCodec (shiftedLiterals (store (w 0)).length literals)++store (w 1)))
  have combined := bodyRun.sequence header
  refine ⟨bodyTime+1+2*(Encoding.natural.encode literals.length).length,?_,?_⟩
  · have positive : 1 ≤ ((store (w 0)).length+1)^2 := Nat.one_le_pow 2 _ (by omega)
    have weighted := Nat.mul_le_mul_left (1+2*(Encoding.natural.encode literals.length).length) positive
    unfold clauseCoefficient
    nlinarith
  · simpa only [emitClause,Function.update_self,Function.update_idem,Encoding.list,shiftedLiterals,
      List.length_map,List.append_assoc] using combined

end Counting.StackMachine.Routine
