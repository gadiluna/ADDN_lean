import Counting.NetworkRecognitionLeaders
import Counting.StackEncodingListReadHeader
import Counting.StackRegisterFrames
import Counting.StackRoutineLists

namespace Counting.StackMachine.NetworkRecognition
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

def leaderHeaderRoles : FullListWorkspace 4 := ⟨![17,1,0,4,18,5,8,9,6,10,11,7,12,13,14,15,16],by decide⟩
def leaderScanRoles : Fin 4 ↪ Fin 21 := ⟨![17,18,19,20],by decide⟩

def leaderPrefix : Routine 19 := sequence (readListHeader 4 leaderHeaderRoles)
  (sequence (ofProgram (ListPrograms.copyProgram 18 18 0 4))
    (sequence (relocate leaderScan leaderScanRoles) (ofProgram (ListPrograms.reverseProgram 19 19 2))))

def leaderPrefixStore (store : Store 19) (values suffix : List Bool) : Store 19 :=
  Function.update (Function.update (Function.update (Function.update store 17 suffix)
    0 (List.replicate values.length true)) 2 values) 20 (List.replicate (values.count true) true)

theorem boolean_sequence (values : List Bool) : Encoding.sequence Encoding.boolean values=values := by
  induction values with
  | nil => rfl
  | cons bit values ih =>
    change [bit]++Encoding.sequence Encoding.boolean values=bit::values
    rw [ih]
    rfl

/-- Parse the actual header, retain the leader vector, and construct the
two unary counters from its explicit bits. All temporary cells are restored. -/
theorem leaderPrefix_executes (store : Store 19) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀r:Fin 21,r.val<17 → r≠1 → store r=[])
    (e18 : store 18=[]) (e19 : store 19=[]) (e20 : store 20=[])
    (values suffix : List Bool)
    (input : store 17=(Encoding.list Encoding.boolean).encode values++suffix) :
    ∃time ≤ 1900*((store 17).length+1)^3,
      Executes leaderPrefix store time (leaderPrefixStore store values suffix) := by
  have headerWork (i:Fin 17) (member:i∈({2,3,4,5,8,11,12,13,14,15,16}:Finset (Fin 17))) :
      store (leaderHeaderRoles i)=[] := by
    fin_cases i
    all_goals simp only [Finset.mem_insert,Finset.mem_singleton] at member
    all_goals first | contradiction | simp [leaderHeaderRoles,work,e18]
  obtain ⟨headerTime,headerBound,headerRun⟩ := readListHeader_canonical 4 leaderHeaderRoles store
    accepted tail status headerWork Encoding.boolean (by intro bit;simp [Encoding.boolean]) values suffix input
  rw [boolean_sequence] at headerRun
  let ready := Function.update (Function.update store 17 (values++suffix)) 18 (List.replicate values.length true)
  have copying := copy_executes 18 (18:Fin 21) 0 4 (by decide) (by decide) (by decide)
    ready (by simp [ready,work])
  rw [show ready 18=List.replicate values.length true by simp [ready],
    show ready 0=[] by simp [ready,work],List.append_nil,List.length_replicate] at copying
  let copied := Function.update ready 0 (List.replicate values.length true)
  let scanned := Function.update (Function.update (Function.update (Function.update copied 17 suffix) 18 [])
    19 values.reverse) 20 (List.replicate (values.count true) true)
  have localRun := leaderScan_executes values suffix (copied ∘ leaderScanRoles)
    (by simp [copied,ready,leaderScanRoles]) (by simp [copied,ready,leaderScanRoles])
  have scanning : Executes (relocate leaderScan leaderScanRoles) copied
      (4*values.length+2*values.count true+1) scanned := by
    apply relocate_executes_frame leaderScan leaderScanRoles copied scanned
      (copied ∘ leaderScanRoles) (leaderScanStore (copied ∘ leaderScanRoles) values suffix) _ rfl
    · intro i
      fin_cases i <;> simp [scanned,copied,ready,leaderScanRoles,leaderScanStore,e19,e20]
    · intro r outside
      have n17 := (outside 0).symm
      have n18 := (outside 1).symm
      have n19 := (outside 2).symm
      have n20 := (outside 3).symm
      change r≠17 at n17
      change r≠18 at n18
      change r≠19 at n19
      change r≠20 at n20
      simp [scanned,n17,n18,n19,n20]
    · exact localRun
  have reversing := reverse_executes 19 (19:Fin 21) 2 (by decide) scanned
  have oldReverse : scanned 19=values.reverse := by simp [scanned]
  have oldOutput : scanned 2=[] := by simp [scanned,copied,ready,work]
  rw [oldReverse,oldOutput,List.append_nil,List.reverse_reverse,List.length_reverse] at reversing
  have final : Function.update (Function.update scanned 19 []) 2 values=leaderPrefixStore store values suffix := by
    funext r
    fin_cases r <;> simp [scanned,copied,ready,leaderPrefixStore,work,e18,e19]
  rw [final] at reversing
  have countBound : values.length ≤ (store 17).length := by
    rw [input]
    change values.length ≤ ((Encoding.natural.encode values.length++Encoding.sequence Encoding.boolean values)++suffix).length
    rw [boolean_sequence]
    simp only [List.length_append]
    omega
  have leaders := List.count_le_length (a:=true) (l:=values)
  have linear : (store 17).length+1 ≤ ((store 17).length+1)^3 := Nat.le_self_pow (by decide) _
  change headerTime ≤ 1820*((store 17).length+1)^3 at headerBound
  exact ⟨headerTime+1+(5*values.length+2+1+(4*values.length+2*values.count true+1+1+(2*values.length+1))),
    by omega,headerRun.sequence (copying.sequence (scanning.sequence reversing))⟩

end Counting.StackMachine.NetworkRecognition
