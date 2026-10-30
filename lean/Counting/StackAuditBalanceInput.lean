import Counting.StackAuditBalanceInputRead
import Counting.StackEncodingListReadHeader
import Counting.EncodingVerifier

namespace Counting.StackMachine.AuditBalance
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

def balanceHeaderRoles : FullListWorkspace 33 :=
  ⟨![42,1,2,3,49,4,5,6,7,8,9,10,11,12,13,14,15],by decide⟩

def balanceSetupFile (anchor : Nat) (vista : Executable.Vista) (weights : Array Nat) : Store 48 :=
  Function.update (Function.update (Function.update
    (balanceInputFile [] anchor.bits (Encoding.vista.encode vista)
      ((Encoding.array Encoding.natural).encode weights)) 1 [true]) 42
      (Encoding.sequence Encoding.node vista.nodes.toList++Encoding.natural.encode vista.bottom))
    49 (List.replicate vista.nodes.size true)

abbrev setupBalanceInput : Routine 48 := sequence (pushBit 1 true)
  (sequence (ofProgram (ListPrograms.copyProgram 47 34 42 47))
    (readListHeader 33 balanceHeaderRoles))

/-- The node counter comes from reading the actual DAG-list header, and
is bounded by its encoded contents. The full DAG remains available for mass sums. -/
theorem setupBalanceInput_executes (anchor : Nat) (vista : Executable.Vista) (weights : Array Nat) :
    ∃ time ≤ 2000*((Encoding.vista.encode vista).length+1)^3,
      Executes setupBalanceInput
        (balanceInputFile [] anchor.bits (Encoding.vista.encode vista)
          ((Encoding.array Encoding.natural).encode weights)) time
        (balanceSetupFile anchor vista weights) := by
  let parsed:=balanceInputFile [] anchor.bits (Encoding.vista.encode vista)
    ((Encoding.array Encoding.natural).encode weights)
  let flagged:=Function.update parsed 1 [true]
  have a:=pushBit_executes (1:Fin 50) true parsed
  change Executes _ parsed 1 flagged at a
  have b:=copy_executes 47 (34:Fin 50) 42 47 (by decide) (by decide) (by decide) flagged
    (by simp [flagged,parsed,balanceInputFile])
  have source : flagged 34=Encoding.vista.encode vista := by simp [flagged,parsed,balanceInputFile]
  have target : flagged 42=[] := by simp [flagged,parsed,balanceInputFile]
  rw [source,target,List.append_nil] at b
  let copied:=Function.update flagged 42 (Encoding.vista.encode vista)
  obtain ⟨headerTime,headerBound,c⟩:=readListHeader_canonical 33 balanceHeaderRoles copied true []
    (by simp [copied,flagged,balanceHeaderRoles])
    (by intro i member;fin_cases i <;> simp_all [copied,flagged,parsed,balanceInputFile,balanceHeaderRoles])
    Encoding.node (by intro node;have positive:=Encoding.node_positive_length node;omega)
    vista.nodes.toList (Encoding.natural.encode vista.bottom)
    (by simp only [copied,balanceHeaderRoles,Function.Embedding.coeFn_mk,Matrix.cons_val_zero,
      Function.update_self];rfl)
  have result : Function.update (Function.update copied (balanceHeaderRoles 0)
      (Encoding.sequence Encoding.node vista.nodes.toList++Encoding.natural.encode vista.bottom))
      (balanceHeaderRoles 4) (List.replicate vista.nodes.toList.length true)=balanceSetupFile anchor vista weights := by
    simp [copied,flagged,parsed,balanceSetupFile,balanceHeaderRoles]
  rw [result] at c
  change headerTime ≤ 1820*((Encoding.vista.encode vista).length+1)^3 at headerBound
  have linear : (Encoding.vista.encode vista).length+1 ≤
      ((Encoding.vista.encode vista).length+1)^3 := Nat.le_self_pow (by decide) _
  exact ⟨_,by omega,a.sequence (b.sequence c)⟩

abbrev prepareBalanceInput : Routine 48 := sequence readBalanceInput setupBalanceInput

theorem prepareBalanceInput_executes (anchor : Nat) (vista : Executable.Vista) (weights : Array Nat) :
    ∃ time ≤ 3000*((balanceInputWord anchor vista weights).length+1)^3,
      Executes prepareBalanceInput
        (balanceInputFile (balanceInputWord anchor vista weights) [] [] []) time
        (balanceSetupFile anchor vista weights) := by
  obtain ⟨readTime,readBound,a⟩:=readBalanceInput_executes anchor vista weights
  obtain ⟨setupTime,setupBound,b⟩:=setupBalanceInput_executes anchor vista weights
  have codeSize : (Encoding.vista.encode vista).length+1 ≤
      (balanceInputWord anchor vista weights).length+1 := by
    simp only [balanceInputWord,AuditPropagation.propagationInputWord,
      AuditPropagation.propagationInputCodec,Encoding.product,Encoding.framed,
      List.length_append,Encoding.frame_length]
    omega
  have setupRaised:=setupBound.trans (Nat.mul_le_mul_left 2000 (Nat.pow_le_pow_left codeSize 3))
  have readRaised:=readBound.trans (Nat.mul_le_mul_left 100
    (Nat.pow_le_pow_right (by omega) (by decide : 2≤3)))
  have one : 1 ≤ ((balanceInputWord anchor vista weights).length+1)^3 := Nat.one_le_pow _ _ (by omega)
  exact ⟨_,by omega,a.sequence b⟩

end Counting.StackMachine.AuditBalance
