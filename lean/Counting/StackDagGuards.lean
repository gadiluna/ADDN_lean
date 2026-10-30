import Counting.StackDagIncrement
import Counting.StackEncodingGuards
import Counting.StackComparePreserving

namespace Counting.StackMachine.DagValidation
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

def positivePreserving (extra : Nat) (w : Fin 4 ↪ Fin (extra+4)) : Routine (extra+2) :=
  sequence (ofProgram (ListPrograms.copyProgram (extra+1) (w 0) (w 2) (w 3)))
    (positiveGuard (extra+2) (w 2) (w 1))

theorem positivePreserving_executes (extra : Nat) (w : Fin 4 ↪ Fin (extra+4))
    (store : Store (extra+2)) (accepted : Bool) (tail : List Bool)
    (flag : store (w 1)=accepted::tail) (copyEmpty : store (w 2)=[]) (scratchEmpty : store (w 3)=[]) :
    Executes (positivePreserving extra w) store (6*(store (w 0)).length+12)
      (Function.update store (w 1) ((accepted && lastPayloadBit false (store (w 0)))::tail)) := by
  have ne (i j : Fin 4) (h : i≠j) : w i≠w j:=fun equal=>h (w.injective equal)
  have copying:=copy_executes (extra+1) (w 0) (w 2) (w 3) (ne 0 2 (by decide))
    (ne 0 3 (by decide)) (ne 2 3 (by decide)) store scratchEmpty
  rw [copyEmpty,List.append_nil] at copying
  let copied:=Function.update store (w 2) (store (w 0))
  have checking:=positiveGuard_executes (extra+2) (w 2) (w 1) (ne 2 1 (by decide)) copied accepted tail
    (by simp [copied,w.injective.eq_iff,flag])
  have reset : Function.update copied (w 2) []=store := by
    simp only [copied,Function.update_idem]
    rw [←copyEmpty,Function.update_eq_self]
  simp only [copied,Function.update_self] at checking
  rw [show Function.update (Function.update store (w 2) (store (w 0))) (w 2) []=store from reset] at checking
  have composed:=copying.sequence checking
  convert composed using 1 <;> first | rfl | omega

def leGuard (extra : Nat) (w : Fin 6 ↪ Fin (extra+6)) : Routine (extra+4) :=
  sequence (Binary.preservingComparison extra w) (ofProgram (combineFlagsProgram (extra+4) (w 2)))

theorem leGuard_executes (extra : Nat) (w : Fin 6 ↪ Fin (extra+6))
    (store : Store (extra+4)) (accepted : Bool) (tail : List Bool)
    (flag : store (w 2)=accepted::tail) (a : store (w 3)=[]) (b : store (w 4)=[]) (c : store (w 5)=[]) :
    Executes (leGuard extra w) store
      (Binary.preservingCompareCost (store (w 0)) (store (w 1))+4)
      (Function.update store (w 2)
        ((accepted && Binary.compareBits true (store (w 0)) (store (w 1)))::tail)) := by
  have compared:=Binary.preservingComparison_executes extra w store a b c
  let checked:=Function.update store (w 2)
    (Binary.compareBits true (store (w 0)) (store (w 1))::store (w 2))
  have combined:=combineFlags_executes (extra+4) (w 2) checked accepted
    (Binary.compareBits true (store (w 0)) (store (w 1))) tail (by simp [checked,flag])
  simp only [checked,Function.update_idem] at combined
  exact compared.sequence combined

def equalityGuard (extra : Nat) (w : Fin 6 ↪ Fin (extra+6)) : Routine (extra+4) :=
  sequence (Compare.preservingEquality extra w) (ofProgram (combineFlagsProgram (extra+4) (w 2)))

theorem equalityGuard_executes (extra : Nat) (w : Fin 6 ↪ Fin (extra+6))
    (store : Store (extra+4)) (accepted : Bool) (tail : List Bool)
    (flag : store (w 2)=accepted::tail) (a : store (w 3)=[]) (b : store (w 4)=[]) (c : store (w 5)=[]) :
    Executes (equalityGuard extra w) store
      (Compare.preservingCost (store (w 0)) (store (w 1))+4)
      (Function.update store (w 2) ((accepted && decide (store (w 0)=store (w 1)))::tail)) := by
  have compared:=Compare.preservingEquality_executes extra w store a b c
  let checked:=Function.update store (w 2) (decide (store (w 0)=store (w 1))::store (w 2))
  have combined:=combineFlags_executes (extra+4) (w 2) checked accepted
    (decide (store (w 0)=store (w 1))) tail (by simp [checked,flag])
  simp only [checked,Function.update_idem] at combined
  exact compared.sequence combined

end Counting.StackMachine.DagValidation
