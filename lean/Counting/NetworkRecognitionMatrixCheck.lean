import Counting.NetworkRecognitionMatrix
import Counting.NetworkRecognitionBFS
import Counting.NetworkRecognitionSemantics

namespace Counting.StackMachine.NetworkRecognition
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000

def matrixRoles : Fin 21 ↪ Fin 26 := ⟨fun r=>⟨r.val,by omega⟩,by intro a b equal;exact Fin.ext (congrArg (fun r:Fin 26=>r.val) equal)⟩
def matrixBfsRoles : Fin 24 ↪ Fin 26 :=
  ⟨![2,3,0,4,5,6,7,8,9,10,11,12,13,14,15,16,18,19,20,1,21,22,23,24],by decide⟩

def matrixCheck : Routine 24 := sequence (relocate matrixPrefix matrixRoles)
  (sequence (relocate breadthFirst matrixBfsRoles) (clear 2))

def matrixAccepted (width:Nat) (rows:List (List Nat)) : Bool :=
  matrixShape width rows && DirectedCounting.strongConnectivityCheck
    (RealizabilityVerifier.BitGraph.edge width (adjacencyBits rows))

def matrixCheckStore (store:Store 24) (accepted:Bool) (tail:List Bool)
    (rows:List (List Nat)) (suffix:List Bool) : Store 24 :=
  Function.update (Function.update store 17 suffix) 1
    ((accepted && matrixAccepted (store 0).length rows)::tail)

/-- Actual dimension checks and actual BFS, with all temporary matrices and
masks erased. The unary width is an explicit agent-count word. -/
theorem matrixCheck_executes (store:Store 24) (accepted:Bool) (tail:List Bool)
    (status:store 1=accepted::tail)
    (work:∀r:Fin 26,r≠0 → r≠1 → r≠17 → r≠25 → store r=[])
    (unary:store 0=List.replicate (store 0).length true)
    (rows:List (List Nat)) (suffix:List Bool)
    (input:store 17=(Encoding.list (Encoding.list Encoding.natural)).encode rows++suffix) :
    ∃time ≤ 500010000*((store 17).length+(store 0).length+1)^6,
      Executes matrixCheck store time (matrixCheckStore store accepted tail rows suffix) := by
  let localStore:=store ∘ matrixRoles
  have localWork (r:Fin 21) (small:r.val<17) (n0:r≠0) (n1:r≠1) : localStore r=[] := by
    apply work
    · intro equal;apply n0;apply Fin.ext;exact congrArg (fun r:Fin 26=>r.val) equal
    · intro equal;apply n1;apply Fin.ext;exact congrArg (fun r:Fin 26=>r.val) equal
    · intro equal;have same:=congrArg Fin.val equal;change r.val=17 at same;omega
    · intro equal;have same:=congrArg Fin.val equal;change r.val=25 at same;omega
  obtain ⟨matrixTime,matrixBound,matrixRun⟩:=matrixPrefix_executes localStore accepted tail status localWork
    (work 18 (by decide) (by decide) (by decide) (by decide))
    (work 19 (by decide) (by decide) (by decide) (by decide))
    (work 20 (by decide) (by decide) (by decide) (by decide)) rows suffix input
  let built:=Function.update (Function.update (Function.update store 17 suffix)
    1 ((accepted && matrixShape (store 0).length rows)::tail)) 2 (adjacencyBits rows)
  have building : Executes (relocate matrixPrefix matrixRoles) store matrixTime built := by
    apply relocate_executes_frame matrixPrefix matrixRoles store built localStore
      (matrixPrefixStore localStore accepted tail rows suffix) matrixTime rfl
    · intro i
      fin_cases i <;> simp [built,matrixPrefixStore,localStore,matrixRoles]
    · intro r outside
      have n1: r≠1:=by simpa [matrixRoles] using (outside 1).symm
      have n2: r≠2:=by simpa [matrixRoles] using (outside 2).symm
      have n17: r≠17:=by simpa [matrixRoles] using (outside 17).symm
      simp [built,n1,n2,n17]
    · exact matrixRun
  let bfsStore:=built ∘ matrixBfsRoles
  have bfsEmpty : RealizabilityCheck.RowEmpty bfsStore := by
    intro r n0 n2 n17 n18 n19 n23
    fin_cases r <;> first | contradiction | simp [bfsStore,built,matrixBfsRoles,work]
  obtain ⟨bfsTime,bfsBound,bfsRun⟩:=breadthFirst_executes bfsStore (store 0).length
    (accepted && matrixShape (store 0).length rows) tail
    (by simpa [bfsStore,built,matrixBfsRoles] using unary)
    (by simp [bfsStore,built,matrixBfsRoles]) bfsEmpty
    (by simp [bfsStore,built,matrixBfsRoles,work])
    (by simp [bfsStore,built,matrixBfsRoles,work])
    (by simp [bfsStore,built,matrixBfsRoles,work])
  have adjacency : bfsStore 0=adjacencyBits rows := by simp [bfsStore,built,matrixBfsRoles]
  rw [adjacency] at bfsBound bfsRun
  let checked:=Function.update built 1 ((accepted && matrixAccepted (store 0).length rows)::tail)
  have checking : Executes (relocate breadthFirst matrixBfsRoles) built bfsTime checked := by
    apply relocate_executes_frame breadthFirst matrixBfsRoles built checked bfsStore
      (Function.update bfsStore 19 (((accepted && matrixShape (store 0).length rows) &&
        DirectedCounting.strongConnectivityCheck
          (RealizabilityVerifier.BitGraph.edge (store 0).length (adjacencyBits rows)))::tail)) bfsTime rfl
    · intro i
      fin_cases i <;> simp [checked,matrixAccepted,Bool.and_assoc,bfsStore,matrixBfsRoles]
    · intro r outside
      have n1:r≠1:=by simpa [matrixBfsRoles] using (outside 19).symm
      simp [checked,n1]
    · exact bfsRun
  have clearing:=clear_executes (2:Fin 26) checked
  rw [show checked 2=adjacencyBits rows by simp [checked,built]] at clearing
  have final : Function.update checked 2 []=matrixCheckStore store accepted tail rows suffix := by
    funext r
    by_cases n1:r=1 <;> by_cases n2:r=2 <;> by_cases n17:r=17 <;>
      simp [checked,built,matrixCheckStore,n1,n2,n17,work]
  rw [final] at clearing
  have bitLength : (adjacencyBits rows).length ≤ (store 17).length := by
    have bounded:=adjacencyBits_length_le rows
    rw [input]
    change _ ≤ ((Encoding.natural.encode rows.length++Encoding.sequence (Encoding.list Encoding.natural) rows)++suffix).length
    simp only [List.length_append];omega
  let S:=(store 17).length+(store 0).length+1
  have base:S=(store 17).length+(store 0).length+1:=rfl
  change matrixTime ≤ 4000*S^4 at matrixBound
  have bfsLimit:bfsTime ≤ 500000000*S^6:=by apply bfsBound.trans;gcongr;omega
  have lower:S^4≤S^6:=Nat.pow_le_pow_right (by omega) (by decide)
  have linear:S≤S^6:=Nat.le_self_pow (by decide) _
  refine ⟨matrixTime+1+(bfsTime+1+((adjacencyBits rows).length+1)),?_,building.sequence (checking.sequence clearing)⟩
  change _ ≤ 500010000*S^6
  omega

end Counting.StackMachine.NetworkRecognition
