import Counting.NetworkVistaCollect
import Counting.StackEncodingListReadHeader

namespace Counting.StackMachine.NetworkVista
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

def collectViewHeaderRoles : FullListWorkspace 23 :=
  ⟨![21,1,2,3,26,5,6,7,8,9,10,11,12,13,14,15,16],by decide⟩
def collectRowHeaderRoles : FullListWorkspace 23 :=
  ⟨![22,1,2,3,27,5,6,7,8,9,10,11,12,13,14,15,16],by decide⟩

def collectViewHeader : Routine 38 := readListHeader 23 collectViewHeaderRoles
def collectRowHeader : Routine 38 := sequence (readListHeader 23 collectRowHeaderRoles) (clear 27)

theorem collectViewHeader_executes (store:Store 38) (accepted:Bool) (tail:List Bool)
    (status:store 1=accepted::tail) (empty:SenderEmpty store) (e26:store 26=[])
    (views:List Executable.Vista) (suffix:List Bool)
    (input:store 21=(Encoding.list Encoding.vista).encode views++suffix) :
    ∃time ≤1820*((store 21).length+1)^3,
      Executes collectViewHeader store time
        (Function.update (Function.update store 21 (Encoding.sequence Encoding.vista views++suffix))
          26 (List.replicate views.length true)) := by
  have work (i:Fin 17) (member:i∈({2,3,4,5,8,11,12,13,14,15,16}:Finset (Fin 17))):
      store (collectViewHeaderRoles i)=[]:=by
    fin_cases i
    all_goals simp only [Finset.mem_insert,Finset.mem_singleton] at member
    all_goals first | contradiction | simp [collectViewHeaderRoles,empty.1,e26]
  exact readListHeader_canonical 23 collectViewHeaderRoles store accepted tail status work
    Encoding.vista (by intro value;rw [Encoding.vista_length];omega) views suffix input

theorem collectRowHeader_executes (store:Store 38) (accepted:Bool) (tail:List Bool)
    (status:store 1=accepted::tail) (empty:SenderEmpty store)
    (rows:List (Array Nat)) (suffix:List Bool)
    (input:store 22=(Encoding.list (Encoding.array Encoding.natural)).encode rows++suffix) :
    ∃time ≤1830*((store 22).length+1)^3,
      Executes collectRowHeader store time
        (Function.update store 22 (Encoding.sequence (Encoding.array Encoding.natural) rows++suffix)) := by
  have work (i:Fin 17) (member:i∈({2,3,4,5,8,11,12,13,14,15,16}:Finset (Fin 17))):
      store (collectRowHeaderRoles i)=[]:=by
    fin_cases i
    all_goals simp only [Finset.mem_insert,Finset.mem_singleton] at member
    all_goals first | contradiction | simp [collectRowHeaderRoles,empty.1,empty.2]
  obtain ⟨headerTime,headerBound,headerRun⟩:=readListHeader_canonical 23 collectRowHeaderRoles
    store accepted tail status work (Encoding.array Encoding.natural)
    (Encoding.array_length_positive _) rows suffix input
  let parsed:=Function.update (Function.update store 22
    (Encoding.sequence (Encoding.array Encoding.natural) rows++suffix)) 27 (List.replicate rows.length true)
  have clearing:=clear_executes 27 parsed
  have count:parsed 27=List.replicate rows.length true:=by simp [parsed]
  rw [count,List.length_replicate] at clearing
  have final:Function.update parsed 27 []=Function.update store 22
      (Encoding.sequence (Encoding.array Encoding.natural) rows++suffix):=by
    simp [parsed,Function.update_idem,
      empty.2 27 (by decide) (by decide)]
  rw [final] at clearing
  have rowBound:rows.length≤(store 22).length:=by
    have bound:=VerifiedParser.sequence_count_le (Encoding.array_length_positive Encoding.natural) rows
    rw [input]
    change rows.length≤((Encoding.frame rows.length.bits++
      Encoding.sequence (Encoding.array Encoding.natural) rows)++suffix).length
    simp only [List.length_append]
    omega
  have linear:(store 22).length+1≤((store 22).length+1)^3:=Nat.le_self_pow (by decide) _
  change headerTime≤1820*((store 22).length+1)^3 at headerBound
  exact ⟨headerTime+1+(rows.length+1),by omega,headerRun.sequence clearing⟩

end Counting.StackMachine.NetworkVista
