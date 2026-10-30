import Counting.ExternalCNFFormulaLoop
import Counting.ExternalCNFLoopSerialization
import Counting.ExternalThreeSATEncoding

namespace Counting.External.CNFMachine

/-- The recursive generator preserves source clause order and advances the
fresh-variable base by exactly one block at each iteration. -/
theorem formulaRows_eq_finRange (current width : Nat) (clauses : List (List (Nat×Bool))) :
    formulaRows current width clauses=
      (List.finRange clauses.length).flatMap (fun c =>
        clauseRows (current+c.val*(width+1)) width clauses[c.val]) := by
  induction clauses generalizing current with
  | nil => simp [formulaRows]
  | cons clause rest ih =>
      simp only [formulaRows,List.length_cons,List.finRange_succ,List.flatMap_cons,
        List.flatMap_map,Fin.val_zero,Nat.zero_mul,Nat.add_zero,List.getElem_cons_zero,
        Fin.val_succ,List.getElem_cons_succ,ih]
      congr 1
      apply congrArg (fun block => (List.finRange rest.length).flatMap block)
      funext c
      congr 1
      ring

theorem formulaRows_map_eq_finRange {α : Type} (current width : Nat) (clauses : List α)
    (encode : α → List (Nat×Bool)) :
    formulaRows current width (clauses.map encode)=
      (List.finRange clauses.length).flatMap (fun c =>
        clauseRows (current+c.val*(width+1)) width (encode clauses[c.val])) := by
  induction clauses generalizing current with
  | nil => simp [formulaRows]
  | cons clause rest ih =>
      simp only [List.map_cons,formulaRows,List.length_cons,List.finRange_succ,List.flatMap_cons,
        List.flatMap_map,Fin.val_zero,Nat.zero_mul,Nat.add_zero,List.getElem_cons_zero,
        Fin.val_succ,List.getElem_cons_succ,ih]
      congr 1
      apply congrArg (fun block => (List.finRange rest.length).flatMap block)
      funext c
      congr 1
      ring

/-- The complete runtime row stream is the exact ordered mathematical
3SAT output, including empty clauses and repeated terminal literals. -/
theorem formulaRows_eq_serialRaw {n : Nat} (formula : CNF n) :
    formulaRows n formula.width (formula.map (List.map CNFEncoding.literalRaw))=
      (List.finRange formula.length).flatMap formula.serialRawBlock := by
  rw [formulaRows_map_eq_finRange]
  apply congrArg (fun block => (List.finRange formula.length).flatMap block)
  funext c
  exact gateRows_terminals_eq_serialRawBlock formula c

theorem formulaRows_eq_reducedInput {n : Nat} (formula : CNF n) :
    CNFEncoding.toRaw (reducedInput ⟨n,formula⟩)=
      (List.replicate formula.targetVariables true,
       formulaRows n formula.width (formula.map (List.map CNFEncoding.literalRaw))) := by
  rw [formulaRows_eq_serialRaw]
  exact CNF.toThreeSAT_toRaw_serial formula

end Counting.External.CNFMachine
