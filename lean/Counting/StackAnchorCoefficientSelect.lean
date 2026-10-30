import Counting.StackAnchorCoefficientRead

namespace Counting.StackMachine.AnchorCoefficient
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

abbrev retainDegree : Routine 32 := sequence (Compare.preservingEquality 28 equalityRoles)
  (branchRoutine 32 (skip 32) (clear 26))

def chargedDegree (node : Executable.Node) (parent : Nat) : Nat :=
  if node.parent==some parent then node.degree else 0

def coefficient (node : Executable.Node) (parent : Nat) : Rat :=
  (Executable.countFrom node parent:Rat)-(chargedDegree node parent:Rat)

theorem parentCode_eq (node : Executable.Node) (parent : Nat) :
    DagValidation.parentCode node=parent+1 ↔ node.parent=some parent := by
  cases h : node.parent <;> simp [DagValidation.parentCode,h]

theorem degree_choice (node : Executable.Node) (parent : Nat) :
    (if (DagValidation.parentCode node).bits=(parent+1).bits then node.degree.bits else [])=
      (chargedDegree node parent).bits := by
  simp only [Encoding.bits_injective.eq_iff,parentCode_eq]
  by_cases equal : node.parent=some parent <;> simp [chargedDegree,equal]

theorem retainDegree_executes (store : Store 32) (one : store 1=[]) (two : store 2=[])
    (three : store 3=[]) (flag : store 32=[]) :
    ∃ time  ≤  6*((store 24).length+(store 28).length)+(store 26).length+14,
      Executes retainDegree store time
        (Function.update store 26 (if store 24=store 28 then store 26 else [])) := by
  have compared := Compare.preservingEquality_executes 28 equalityRoles store one two three
  have cost := Compare.preservingCost_le (store 24) (store 28)
  change Executes _ _ (Compare.preservingCost (store 24) (store 28))
    (Function.update store 32 (decide (store 24=store 28)::store 32)) at compared
  rw [flag] at compared
  have clearedFlag (bit : Bool) : Function.update (Function.update store 32 [bit]) 32 []=store := by
    simp only [Function.update_idem,←flag,Function.update_eq_self]
  by_cases equal : store 24=store 28
  · have truth : decide (store 24=store 28)=true := by simp [equal]
    rw [truth] at compared
    have branch := branch_executes_true (32:Fin 34) (skip 32) (clear 26)
      (Function.update store 32 [true]) store [] 0 (by simp)
      ((clearedFlag true).symm ▸ skip_executes store)
    have total := compared.sequence branch
    refine ⟨Compare.preservingCost (store 24) (store 28)+1+(1+0),by omega,?_⟩
    simpa only [retainDegree,if_pos equal,Function.update_eq_self] using total
  · have falsity : decide (store 24=store 28)=false := by simp [equal]
    rw [falsity] at compared
    have cleared := clear_executes (26:Fin 34) store
    have branch := branch_executes_false (32:Fin 34) (skip 32) (clear 26)
      (Function.update store 32 [false]) (Function.update store 26 []) [] _ (by simp)
      (by rw [clearedFlag];exact cleared)
    have total := compared.sequence branch
    refine ⟨Compare.preservingCost (store 24) (store 28)+1+(1+((store 26).length+1)),by omega,?_⟩
    simpa only [retainDegree,if_neg equal] using total

theorem subtract_executes (count degree : Nat) (input query result level parent leader successor flag : List Bool) :
    ∃ time  ≤  10000*(count.size+degree.size+1),
      Executes subtract (file input query result level parent leader degree.bits count.bits successor flag) time
        (file input query (Encoding.rational.encode ((count:Rat)-degree)++result)
          level parent leader [] [] successor flag) := by
  obtain ⟨time,bounded,ran⟩ := AnchorDifference.difference_executes count degree result
  refine ⟨time,bounded,?_⟩
  apply relocate_executes_frame AnchorDifference.difference differenceRoles _ _ _ _ time _ _ _ ran
  · funext r;fin_cases r <;> simp [file,AnchorDifference.file,differenceRoles]
  · intro r;fin_cases r <;> simp [file,AnchorDifference.file,differenceRoles]
  · intro r outside
    have n22 : r≠22 := by intro eq;subst r;exact outside 15 rfl
    have n26 : r≠26 := by intro eq;subst r;exact outside 13 rfl
    have n27 : r≠27 := by intro eq;subst r;exact outside 12 rfl
    simp [file,n22,n26,n27]

end Counting.StackMachine.AnchorCoefficient
