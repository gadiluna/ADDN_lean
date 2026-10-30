import Counting.NetworkVistaInitialLoop
import Counting.NetworkRecognitionLeaderHeader

namespace Counting.StackMachine.NetworkVista
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

def initialHeaderRoles : FullListWorkspace 4 := NetworkRecognition.leaderHeaderRoles
def initialLoopRoles : Fin 3 ↪ Fin 21 := ⟨![17,19,18],by decide⟩

def initialHeader : Routine 19 := sequence (listHeaderRoutine 4 initialHeaderRoles)
  (ofProgram (combineFlagsProgram 19 1))

def initialHeaderStore (store:Store 19) (leaders suffix:List Bool) : Store 19 :=
  Function.update (Function.update (Function.update store 17 (leaders++suffix))
    4 (Encoding.natural.encode leaders.length)) 18 (List.replicate leaders.length true)

theorem initialHeader_executes (store:Store 19) (accepted:Bool) (tail:List Bool)
    (status:store 1=accepted::tail) (work:∀r:Fin 21,r.val<17 → r≠1 → store r=[])
    (e18:store 18=[]) (leaders suffix:List Bool)
    (input:store 17=(Encoding.list Encoding.boolean).encode leaders++suffix) :
    ∃time ≤ 1810*((store 17).length+1)^3,
      Executes initialHeader store time (initialHeaderStore store leaders suffix) := by
  have empty (i:Fin 17) (member:i∈({2,3,4,5,8,11,12,13,14,15,16}:Finset (Fin 17))):
      store (initialHeaderRoles i)=[]:=by
    fin_cases i
    all_goals simp only [Finset.mem_insert,Finset.mem_singleton] at member
    all_goals first | contradiction | simp [initialHeaderRoles,NetworkRecognition.leaderHeaderRoles,work,e18]
  obtain ⟨time,bound,reading⟩:=listHeader_executes 4 initialHeaderRoles store empty
  let header:=listHeaderStore 4 initialHeaderRoles store
  have good:=listHeader_natural Encoding.boolean (by intro value;simp [Encoding.boolean]) leaders suffix
  have decoded:Encoding.unframe (store 17)=some (leaders.length.bits,leaders++suffix):=by
    rw [input]
    change Encoding.unframe ((Encoding.frame leaders.length.bits++Encoding.sequence Encoding.boolean leaders)++suffix)=_
    rw [List.append_assoc,Encoding.unframe_frame,NetworkRecognition.boolean_sequence]
  have nextStatus:header 1=true::accepted::tail:=by
    simp [header,listHeaderStore,initialHeaderRoles,NetworkRecognition.leaderHeaderRoles,input,good.2.2,status]
  have combining:=combineFlags_executes 19 1 header accepted true tail nextStatus
  have count:listCount (store 17)=leaders.length:=by rw [input];exact good.2.1
  have final:Function.update header 1 ((accepted && true)::tail)=initialHeaderStore store leaders suffix:=by
    funext r
    by_cases n1:r=1 <;> by_cases n4:r=4 <;> by_cases n17:r=17 <;> by_cases n18:r=18 <;>
      simp [header,listHeaderStore,initialHeaderRoles,NetworkRecognition.leaderHeaderRoles,initialHeaderStore,
        n1,n4,n17,n18,status,unframePayload,unframeSuffix,decoded,count,Encoding.natural]
  rw [final] at combining
  have one:1≤((store 17).length+1)^3:=Nat.one_le_pow _ _ (by omega)
  change time≤1800*((store 17).length+1)^3 at bound
  exact ⟨time+1+3,by omega,reading.sequence combining⟩

end Counting.StackMachine.NetworkVista
