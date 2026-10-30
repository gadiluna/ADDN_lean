import Counting.ExternalCNFLoop
import Counting.ExternalCNFThreeSATSerialization

namespace Counting.External.CNFMachine

/-- The concrete recursive loop emits gate blocks in increasing position
order; exhaustion uses the same fixed terminal literal at every position. -/
theorem gateRows_eq_finRange (current terminal count : Nat) (literals : List (Nat×Bool)) :
    gateRows current terminal count literals=
      (List.finRange count).flatMap (fun j =>
        gateClauses (current+j.val) ((literals.drop j.val).headD (terminal,true))) := by
  induction count generalizing current literals with
  | zero => simp [gateRows]
  | succ count ih =>
      simp only [gateRows,List.finRange_succ,List.flatMap_cons,List.flatMap_map,
        Fin.val_zero,Nat.add_zero,List.drop_zero,ih]
      congr 1
      apply congrArg (fun block => (List.finRange count).flatMap block)
      funext j
      simp only [Fin.val_succ,List.drop_tail]
      congr 1
      omega

theorem clause_atomRaw_drop {n : Nat} (formula : CNF n) (c : Fin formula.length) (position : Nat) :
    (((formula.clause c).map CNFEncoding.literalRaw).drop position).headD
      (n+c.val*(formula.width+1)+formula.width,true)=formula.atomRaw c position := by
  simp only [List.headD_eq_head?_getD,List.head?_drop,List.getElem?_map,CNF.atomRaw]
  cases entry : (formula.clause c)[position]? with
  | none => simp [CNF.freshRaw]
  | some literal => simp

/-- The complete emitted clause block, including both repeated terminal
triples, agrees with the existing order-sensitive 3SAT serialization. -/
theorem gateRows_terminals_eq_serialRawBlock {n : Nat} (formula : CNF n) (c : Fin formula.length) :
    gateRows (n+c.val*(formula.width+1)) (n+c.val*(formula.width+1)+formula.width)
      formula.width ((formula.clause c).map CNFEncoding.literalRaw)++
      [List.replicate 3 (n+c.val*(formula.width+1),true),
       List.replicate 3 (n+c.val*(formula.width+1)+formula.width,false)] =
      formula.serialRawBlock c := by
  rw [gateRows_eq_finRange]
  simp only [CNF.serialRawBlock,CNF.freshRaw,CNF.negateRaw,Nat.add_zero,Bool.not_true]
  congr 1
  apply congrArg (fun block => (List.finRange formula.width).flatMap block)
  funext j
  rw [clause_atomRaw_drop]
  simp only [gateClauses,Nat.add_assoc]

end Counting.External.CNFMachine
