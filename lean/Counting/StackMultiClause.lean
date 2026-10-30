import Counting.StackEmitClause

namespace Counting.StackMachine.Routine

abbrev ClauseWorkspace (extra : Nat) := Fin 8 ↪ Fin (extra+8)

structure LiteralTemplate where
  source : Fin 4
  offset : Nat
  positive : Bool

def sourceSelection (source : Fin 4) : Fin 5 ↪ Fin 8 where
  toFun := ![source.castAdd 4,4,5,6,7]
  inj' := by
    intro first second same
    fin_cases first <;> fin_cases second <;> try rfl
    all_goals
      have values := congrArg Fin.val same
      have bounded := source.isLt
      norm_num at values <;> omega

def ClauseWorkspace.literalRoles (w : ClauseWorkspace extra) (source : Fin 4) : PowerWorkspace (extra+3) :=
  (sourceSelection source).trans w

@[simp] theorem ClauseWorkspace.literalRoles_source (w : ClauseWorkspace extra) (source : Fin 4) :
    w.literalRoles source 0 = w (source.castAdd 4) := rfl
@[simp] theorem ClauseWorkspace.literalRoles_output (w : ClauseWorkspace extra) (source : Fin 4) :
    w.literalRoles source 1 = w 4 := rfl
@[simp] theorem ClauseWorkspace.literalRoles_counter (w : ClauseWorkspace extra) (source : Fin 4) :
    w.literalRoles source 2 = w 5 := rfl
@[simp] theorem ClauseWorkspace.literalRoles_binary (w : ClauseWorkspace extra) (source : Fin 4) :
    w.literalRoles source 3 = w 6 := rfl
@[simp] theorem ClauseWorkspace.literalRoles_work (w : ClauseWorkspace extra) (source : Fin 4) :
    w.literalRoles source 4 = w 7 := rfl

theorem ClauseWorkspace.source_ne_output (w : ClauseWorkspace extra) (source : Fin 4) :
    w (source.castAdd 4) ≠ w 4 := by
  intro same
  have values := congrArg Fin.val (w.injective same)
  have bounded := source.isLt
  simp only [Fin.val_castAdd] at values
  omega

def LiteralTemplate.value (w : ClauseWorkspace extra) (store : Fin (extra+8) → List Bool)
    (literal : LiteralTemplate) : Nat × Bool :=
  ((store (w (literal.source.castAdd 4))).length+literal.offset,literal.positive)

def emitMultiList (extra : Nat) (w : ClauseWorkspace extra) : List LiteralTemplate → Routine (extra+6)
  | [] => skip (extra+6)
  | literal::rest => sequence (emitMultiList extra w rest)
      (emitOffsetLiteral (extra+3) (w.literalRoles literal.source) literal.offset literal.positive)

def multiListCoefficient : List LiteralTemplate → Nat
  | [] => 0
  | literal::rest => multiListCoefficient rest+1+offsetLiteralCoefficient literal.offset

theorem emitMultiList_executes (extra : Nat) (w : ClauseWorkspace extra) (literals : List LiteralTemplate)
    (store : Fin (extra+8) → List Bool) (bound : Nat)
    (bounded : ∀ source : Fin 4, (store (w (source.castAdd 4))).length ≤ bound)
    (counterEmpty : store (w 5)=[]) (binaryEmpty : store (w 6)=[]) (workEmpty : store (w 7)=[]) :
    ∃ transitions ≤ multiListCoefficient literals*(bound+1)^2,
      Executes (emitMultiList extra w literals) store transitions
        (Function.update store (w 4)
          (Encoding.sequence literalCodec (literals.map (LiteralTemplate.value w store))++store (w 4))) := by
  induction literals generalizing store with
  | nil =>
      refine ⟨0,by simp [multiListCoefficient],?_⟩
      simpa only [emitMultiList,List.map_nil,Encoding.sequence,List.nil_append,Function.update_eq_self] using skip_executes store
  | cons literal rest ih =>
      obtain ⟨tailTime,tailBound,tailRun⟩ := ih store bounded counterEmpty binaryEmpty workEmpty
      let middle := Function.update store (w 4)
        (Encoding.sequence literalCodec (rest.map (LiteralTemplate.value w store))++store (w 4))
      obtain ⟨headTime,headBound,headRun⟩ := emitOffsetLiteral_executes (extra+3) (w.literalRoles literal.source)
        literal.offset literal.positive middle
        (by simp [middle,w.injective.eq_iff,counterEmpty])
        (by simp [middle,w.injective.eq_iff,binaryEmpty])
        (by simp [middle,w.injective.eq_iff,workEmpty])
      have combined := tailRun.sequence headRun
      refine ⟨tailTime+1+headTime,?_,?_⟩
      · simp only [ClauseWorkspace.literalRoles_source,middle,Function.update_of_ne (w.source_ne_output _)] at headBound
        have scaled := Nat.mul_le_mul_left (offsetLiteralCoefficient literal.offset)
          (Nat.pow_le_pow_left (Nat.add_le_add_right (bounded literal.source) 1) 2)
        have positive : 1 ≤ (bound+1)^2 := Nat.one_le_pow 2 _ (by omega)
        unfold multiListCoefficient
        nlinarith
      · simpa only [emitMultiList,middle,ClauseWorkspace.literalRoles_source,ClauseWorkspace.literalRoles_output,
          Function.update_of_ne (w.source_ne_output _),Function.update_self,Function.update_idem,
          List.map_cons,Encoding.sequence,LiteralTemplate.value,List.append_assoc] using combined

def emitMultiClause (extra : Nat) (w : ClauseWorkspace extra) (literals : List LiteralTemplate) : Routine (extra+6) :=
  sequence (emitMultiList extra w literals) (prepend (w 4) (Encoding.natural.encode literals.length))

def multiClauseCoefficient (literals : List LiteralTemplate) : Nat :=
  multiListCoefficient literals+1+2*(Encoding.natural.encode literals.length).length

/-- A runtime clause may refer to four independent positions, with fixed
symbol offsets. Its execution preserves all four bases and empties scratch. -/
theorem emitMultiClause_executes (extra : Nat) (w : ClauseWorkspace extra) (literals : List LiteralTemplate)
    (store : Fin (extra+8) → List Bool) (bound : Nat)
    (bounded : ∀ source : Fin 4, (store (w (source.castAdd 4))).length ≤ bound)
    (counterEmpty : store (w 5)=[]) (binaryEmpty : store (w 6)=[]) (workEmpty : store (w 7)=[]) :
    ∃ transitions ≤ multiClauseCoefficient literals*(bound+1)^2,
      Executes (emitMultiClause extra w literals) store transitions
        (Function.update store (w 4)
          ((Encoding.list literalCodec).encode (literals.map (LiteralTemplate.value w store))++store (w 4))) := by
  obtain ⟨bodyTime,bodyBound,bodyRun⟩ := emitMultiList_executes extra w literals store bound bounded counterEmpty binaryEmpty workEmpty
  have header := prepend_executes (w 4) (Encoding.natural.encode literals.length)
    (Function.update store (w 4)
      (Encoding.sequence literalCodec (literals.map (LiteralTemplate.value w store))++store (w 4)))
  have combined := bodyRun.sequence header
  refine ⟨bodyTime+1+2*(Encoding.natural.encode literals.length).length,?_,?_⟩
  · have positive : 1 ≤ (bound+1)^2 := Nat.one_le_pow 2 _ (by omega)
    have weighted := Nat.mul_le_mul_left (1+2*(Encoding.natural.encode literals.length).length) positive
    unfold multiClauseCoefficient
    nlinarith
  · simpa only [emitMultiClause,Function.update_self,Function.update_idem,Encoding.list,
      List.length_map,List.append_assoc] using combined

end Counting.StackMachine.Routine
