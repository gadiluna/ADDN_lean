import Counting.StackEmitNatural

namespace Counting.StackMachine.Routine

/-- Emit a signed variable whose identifier is supplied as a unary counter. -/
def emitLiteral (extra : Nat) (w : PowerWorkspace extra) (positive : Bool) : Routine (extra+3) :=
  sequence (pushBit (w 1) positive) (emitNatural extra w)

theorem emitLiteral_executes (extra : Nat) (w : PowerWorkspace extra) (positive : Bool)
    (store : Fin (extra+5) → List Bool) (counterEmpty : store (w 2) = [])
    (binaryEmpty : store (w 3) = []) (workEmpty : store (w 4) = []) :
    ∃ transitions ≤ 22*((store (w 0)).length+1)^2,
      Executes (emitLiteral extra w positive) store transitions
        (Function.update store (w 1)
          ((Encoding.product Encoding.natural Encoding.boolean).encode ((store (w 0)).length,positive)++store (w 1))) := by
  let pushed := Function.update store (w 1) (positive::store (w 1))
  obtain ⟨time,bounded,emitted⟩ := emitNatural_executes extra w pushed
    (by simp [pushed,w.injective.eq_iff,counterEmpty])
    (by simp [pushed,w.injective.eq_iff,binaryEmpty])
    (by simp [pushed,w.injective.eq_iff,workEmpty])
  have combined := (pushBit_executes (w 1) positive store).sequence emitted
  refine ⟨1+1+time,?_,?_⟩
  · simp only [pushed,Function.update_of_ne (workspace_ne w (by decide : (0 : Fin 5) ≠ 1))] at bounded
    have positiveSquare : 1 ≤ ((store (w 0)).length+1)^2 := Nat.one_le_pow 2 _ (by omega)
    omega
  · simpa only [emitLiteral,pushed,Function.update_self,
      Function.update_of_ne (workspace_ne w (by decide : (0 : Fin 5) ≠ 1)),
      Function.update_idem,Encoding.product,Encoding.boolean,List.append_assoc,List.singleton_append] using combined

/-- Emit the explicit variable table used by the CNF codec. No universe
cardinality is hidden in a binary header: the output contains all markers. -/
def emitVariableTable (extra : Nat) (w : PowerWorkspace extra) : Routine (extra+3) :=
  sequence (ofProgram (ListPrograms.copyProgram (extra+2) (w 0) (w 1) (w 4))) (emitNatural extra w)

theorem sequence_boolean (word : List Bool) : Encoding.sequence Encoding.boolean word = word := by
  induction word with
  | nil => rfl
  | cons bit word ih => exact congrArg (List.cons bit) ih

theorem emitVariableTable_executes (extra : Nat) (w : PowerWorkspace extra) (size : Nat)
    (store : Fin (extra+5) → List Bool) (unary : store (w 0) = List.replicate size true)
    (counterEmpty : store (w 2) = []) (binaryEmpty : store (w 3) = []) (workEmpty : store (w 4) = []) :
    ∃ transitions ≤ 28*(size+1)^2,
      Executes (emitVariableTable extra w) store transitions
        (Function.update store (w 1)
          ((Encoding.list Encoding.boolean).encode (List.replicate size true)++store (w 1))) := by
  let copied := Function.update store (w 1) (store (w 0)++store (w 1))
  have copy : Executes (ofProgram (ListPrograms.copyProgram (extra+2) (w 0) (w 1) (w 4))) store
      (5*size+2) copied := by
    obtain ⟨finish,run,halted,finalStore⟩ := copy_executes (extra+2) (w 0) (w 1) (w 4)
      (workspace_ne w (by decide)) (workspace_ne w (by decide)) (workspace_ne w (by decide)) store workEmpty
    refine ⟨finish,?_,halted,?_⟩
    · simpa only [unary,List.length_replicate] using run
    · rw [finalStore]
      funext register
      by_cases equal : register = w 1
      · subst register; simp [copied]
      · simp [copied,Function.update,equal]
        intro same
        exact False.elim (equal same)
  obtain ⟨time,bounded,emitted⟩ := emitNatural_executes extra w copied
    (by simp [copied,w.injective.eq_iff,counterEmpty])
    (by simp [copied,w.injective.eq_iff,binaryEmpty])
    (by simp [copied,w.injective.eq_iff,workEmpty])
  have combined := copy.sequence emitted
  refine ⟨5*size+2+1+time,?_,?_⟩
  · simp only [copied,Function.update_of_ne (workspace_ne w (by decide : (0 : Fin 5) ≠ 1)),unary,List.length_replicate] at bounded
    nlinarith
  · simpa only [ListPrograms.copyProgram,emitVariableTable,copied,Function.update_self,
      Function.update_of_ne (workspace_ne w (by decide : (0 : Fin 5) ≠ 1)),
      Function.update_idem,unary,List.length_replicate,Encoding.list,sequence_boolean,List.append_assoc] using combined

end Counting.StackMachine.Routine
