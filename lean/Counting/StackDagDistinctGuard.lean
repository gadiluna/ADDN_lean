import Counting.StackDagGuards
import Counting.EncodingDag

/-! A word-distinctness guard, preserving both operands and charging the
comparison, Boolean negation and accumulation. Canonical node encodings
then turn this exact word inequality into structural node inequality. -/
namespace Counting.StackMachine.DagValidation
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

def distinctGuard (extra : Nat) (w : Fin 6 ↪ Fin (extra+6)) : Routine (extra+4):=
  sequence (Compare.preservingEquality extra w)
    (sequence (negateFlag (extra+4) (w 2)) (ofProgram (combineFlagsProgram (extra+4) (w 2))))

theorem distinctGuard_executes (extra : Nat) (w : Fin 6 ↪ Fin (extra+6))
    (store : Store (extra+4)) (accepted : Bool) (tail : List Bool)
    (status : store (w 2)=accepted::tail) (e3 : store (w 3)=[]) (e4 : store (w 4)=[]) (e5 : store (w 5)=[]) :
    Executes (distinctGuard extra w) store (Compare.preservingCost (store (w 0)) (store (w 1))+7)
      (Function.update store (w 2) ((accepted && !decide (store (w 0)=store (w 1)))::tail)) := by
  have compared:=Compare.preservingEquality_executes extra w store e3 e4 e5
  let checked:=Function.update store (w 2) (decide (store (w 0)=store (w 1))::store (w 2))
  have negated:=negateFlag_executes (extra+4) (w 2) checked
    (decide (store (w 0)=store (w 1))) (accepted::tail) (by simp [checked,status])
  let middle:=Function.update checked (w 2) ((!decide (store (w 0)=store (w 1)))::accepted::tail)
  have combined:=combineFlags_executes (extra+4) (w 2) middle accepted
    (!decide (store (w 0)=store (w 1))) tail (by simp [middle])
  have final : Function.update middle (w 2) ((accepted && !decide (store (w 0)=store (w 1)))::tail)=
      Function.update store (w 2) ((accepted && !decide (store (w 0)=store (w 1)))::tail):=by
    simp only [middle,checked,Function.update_idem]
  rw [final] at combined
  convert compared.sequence (negated.sequence combined) using 1; rfl

theorem canonical_nodes_distinct (first second : Executable.Node) :
    (!decide (Encoding.node.encode first=Encoding.node.encode second))=decide (first≠second):=by
  simp [Encoding.node.injective.eq_iff]

end Counting.StackMachine.DagValidation
