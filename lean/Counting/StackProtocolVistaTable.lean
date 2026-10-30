import Counting.StackProtocolVistaDepth
import Counting.StackAuditPrefixTable

namespace Counting.StackMachine.ProtocolVista
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

def tableWord (vista : Executable.Vista) : List Bool :=
  Encoding.sequence Encoding.node vista.nodes.toList++Encoding.natural.encode vista.bottom

def file (vista : Executable.Vista) (depth roots found : List Bool) : Store 50 := fun r=>
  if r=1 then [true] else if r=17 then tableWord vista else if r=20 then List.replicate vista.nodes.size true
  else if r=40 then Encoding.vista.encode vista else if r=42 then depth else if r=43 then roots
  else if r=29 then found else []

abbrev prepareTable : Routine 50 := sequence (move 49 0 40 51)
  (sequence (pushBit 1 true) AuditPrefix.prepareTable)

theorem prepareTable_executes (vista : Executable.Vista) :
    ∃ time≤ 2100*((Encoding.vista.encode vista).length+1)^3,
      Executes prepareTable (inputStore 50 (Encoding.vista.encode vista)) time (file vista [] [] []) := by
  let initial:=inputStore 50 (Encoding.vista.encode vista)
  have a:=move_executes 49 (0:Fin 52) 40 51 (by decide) (by decide) (by decide) initial rfl
  change Executes _ initial (6*(Encoding.vista.encode vista).length+4)
    (Function.update (Function.update initial 40 (Encoding.vista.encode vista++[])) 0 []) at a
  simp only [List.append_nil] at a
  let moved:=Function.update (Function.update initial 40 (Encoding.vista.encode vista)) 0 []
  have b:=pushBit_executes (1:Fin 52) true moved
  have vacant:moved 1=[] := by simp [moved,initial,inputStore]
  rw [vacant] at b
  let flagged:=Function.update moved 1 [true]
  obtain ⟨c,cbound,crun⟩:=AuditPrefix.prepareTable_executes flagged vista
    (by simp [flagged,moved]) true [] (by simp [flagged])
    (by simp [flagged,moved,initial,inputStore]) (by simp [flagged,moved,initial,inputStore])
    (by intro i member;fin_cases i <;> simp_all [flagged,moved,initial,inputStore,AuditPrefix.tableHeaderRoles])
  have target:AuditPrefix.tableFile flagged vista=file vista [] [] [] := by
    funext r;fin_cases r <;> simp [AuditPrefix.tableFile,flagged,moved,initial,inputStore,file,tableWord]
  rw [target] at crun
  have linear:(Encoding.vista.encode vista).length+1≤ ((Encoding.vista.encode vista).length+1)^3:=
    Nat.le_self_pow (by decide) _
  exact ⟨_,by omega,a.sequence (b.sequence crun)⟩

theorem tableWord_length (vista : Executable.Vista) :
    (tableWord vista).length≤ (Encoding.vista.encode vista).length := by
  change (tableWord vista).length≤ (Encoding.natural.encode vista.nodes.size++
    Encoding.sequence Encoding.node vista.nodes.toList++Encoding.natural.encode vista.bottom).length
  simp only [tableWord,List.length_append]
  omega

theorem readDepth_file (vista : Executable.Vista) (valid : vista.valid=true) :
    ∃ time≤ 10000*((Encoding.vista.encode vista).length+1)^4,
      Executes readDepth (file vista [] [] []) time
        (file vista (vista.node vista.bottom).level.bits [] []) := by
  obtain ⟨time,bounded,run⟩:=readDepth_executes (file vista [] [] []) vista valid true [] rfl
    (by intro r small different;fin_cases r <;> simp_all [file]) rfl rfl rfl rfl
    (Encoding.natural.encode vista.bottom) rfl rfl
  have target:Function.update (file vista [] [] []) 42 (vista.node vista.bottom).level.bits=
      file vista (vista.node vista.bottom).level.bits [] [] := by
    funext r;fin_cases r <;> simp [file]
  rw [target] at run
  exact ⟨time,bounded.trans (Nat.mul_le_mul_left 10000
    (Nat.pow_le_pow_left (Nat.add_le_add_right (tableWord_length vista) 1) 4)),run⟩

end Counting.StackMachine.ProtocolVista
