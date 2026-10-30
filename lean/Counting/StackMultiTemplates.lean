import Counting.StackMultiClause
import Counting.StackEmitTemplates

namespace Counting.StackMachine.Routine

def emitMultiClauses (extra : Nat) (w : ClauseWorkspace extra) : List (List LiteralTemplate) → Routine (extra+6)
  | [] => skip (extra+6)
  | clause::rest => sequence (emitMultiClauses extra w rest) (emitMultiClause extra w clause)

def multiClausesCoefficient : List (List LiteralTemplate) → Nat
  | [] => 0
  | clause::rest => multiClausesCoefficient rest+1+multiClauseCoefficient clause

theorem emitMultiClauses_executes (extra : Nat) (w : ClauseWorkspace extra) (clauses : List (List LiteralTemplate))
    (store : Fin (extra+8) → List Bool) (bound : Nat)
    (bounded : ∀ source : Fin 4, (store (w (source.castAdd 4))).length ≤ bound)
    (counterEmpty : store (w 5)=[]) (binaryEmpty : store (w 6)=[]) (workEmpty : store (w 7)=[]) :
    ∃ transitions ≤ multiClausesCoefficient clauses*(bound+1)^2,
      Executes (emitMultiClauses extra w clauses) store transitions
        (Function.update store (w 4)
          (Encoding.sequence clauseCodec (clauses.map (List.map (LiteralTemplate.value w store)))++store (w 4))) := by
  induction clauses generalizing store with
  | nil =>
      refine ⟨0,by simp [multiClausesCoefficient],?_⟩
      simpa only [emitMultiClauses,List.map_nil,Encoding.sequence,List.nil_append,Function.update_eq_self] using skip_executes store
  | cons clause rest ih =>
      obtain ⟨tailTime,tailBound,tailRun⟩ := ih store bounded counterEmpty binaryEmpty workEmpty
      let middle := Function.update store (w 4)
        (Encoding.sequence clauseCodec (rest.map (List.map (LiteralTemplate.value w store)))++store (w 4))
      have middleBounded : ∀ source : Fin 4, (middle (w (source.castAdd 4))).length ≤ bound := by
        intro source
        simpa only [middle,Function.update_of_ne (w.source_ne_output source)] using bounded source
      obtain ⟨headTime,headBound,headRun⟩ := emitMultiClause_executes extra w clause middle bound middleBounded
        (by simp [middle,w.injective.eq_iff,counterEmpty])
        (by simp [middle,w.injective.eq_iff,binaryEmpty])
        (by simp [middle,w.injective.eq_iff,workEmpty])
      have values : LiteralTemplate.value w middle = LiteralTemplate.value w store := by
        funext literal
        simp only [LiteralTemplate.value,middle,Function.update_of_ne (w.source_ne_output literal.source)]
      have combined := tailRun.sequence headRun
      refine ⟨tailTime+1+headTime,?_,?_⟩
      · have positive : 1 ≤ (bound+1)^2 := Nat.one_le_pow 2 _ (by omega)
        unfold multiClausesCoefficient
        nlinarith
      · simpa only [emitMultiClauses,values,middle,Function.update_self,Function.update_idem,
          List.map_cons,Encoding.sequence,List.append_assoc] using combined

end Counting.StackMachine.Routine
