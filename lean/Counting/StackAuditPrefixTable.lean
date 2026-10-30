import Counting.StackAuditPrefixInput
import Counting.StackEncodingListReadHeader
import Counting.EncodingVerifier

namespace Counting.StackMachine.AuditPrefix
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def tableHeaderRoles : FullListWorkspace 35 :=
  ⟨![17,1,2,3,20,4,5,6,7,8,9,10,11,12,13,14,15],by decide⟩

abbrev prepareTable : Routine 50 := sequence (ofProgram (ListPrograms.copyProgram 49 40 17 51))
  (readListHeader 35 tableHeaderRoles)

def tableFile (store : Store 50) (vista : Executable.Vista) : Store 50 :=
  Function.update (Function.update store 17
    (Encoding.sequence Encoding.node vista.nodes.toList++Encoding.natural.encode vista.bottom))
      20 (List.replicate vista.nodes.size true)

/-- The persistent scan table and unary node budget are read from the
actual serialized header, while the entire vista remains available. -/
theorem prepareTable_executes (store : Store 50) (vista : Executable.Vista)
    (source : store 40=Encoding.vista.encode vista)
    (accepted : Bool) (tail : List Bool) (status : store 1=accepted::tail)
    (e17 : store 17=[]) (e51 : store 51=[])
    (empty : ∀ i : Fin 17,i∈({2,3,4,5,8,11,12,13,14,15,16}:Finset (Fin 17)) →
      store (tableHeaderRoles i)=[]) :
    ∃ time ≤ 2000*((Encoding.vista.encode vista).length+1)^3,
      Executes prepareTable store time (tableFile store vista) := by
  have a:=copy_executes 49 (40:Fin 52) 17 51 (by decide) (by decide) (by decide) store e51
  rw [source,e17,List.append_nil] at a
  let copied:=Function.update store 17 (Encoding.vista.encode vista)
  obtain ⟨time,bound,b⟩:=readListHeader_canonical 35 tableHeaderRoles copied accepted tail
    (by simp [copied,tableHeaderRoles,status]) (by
      intro i member
      have different : tableHeaderRoles i≠17 := by
        fin_cases i <;> simp_all [tableHeaderRoles]
      simpa [copied,different] using empty i member)
    Encoding.node (by intro node;exact Encoding.node_positive_length node)
    vista.nodes.toList (Encoding.natural.encode vista.bottom)
    (by simp only [copied,tableHeaderRoles,Function.Embedding.coeFn_mk,Matrix.cons_val_zero,
      Function.update_self];rfl)
  have final : Function.update (Function.update copied (tableHeaderRoles 0)
      (Encoding.sequence Encoding.node vista.nodes.toList++Encoding.natural.encode vista.bottom))
      (tableHeaderRoles 4) (List.replicate vista.nodes.toList.length true)=tableFile store vista := by
    simp [copied,tableHeaderRoles,tableFile]
  rw [final] at b
  change time ≤ 1820*((Encoding.vista.encode vista).length+1)^3 at bound
  have linear : (Encoding.vista.encode vista).length+1 ≤
      ((Encoding.vista.encode vista).length+1)^3 := Nat.le_self_pow (by decide) _
  exact ⟨_,by omega,a.sequence b⟩

end Counting.StackMachine.AuditPrefix
