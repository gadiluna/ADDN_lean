import Counting.NetworkRecognitionMatrixLoop
import Counting.StackRoutineLists

namespace Counting.StackMachine.NetworkRecognition
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

def matrixHeaderRoles : FullListWorkspace 4 := ⟨![17,1,3,4,20,5,8,9,6,10,11,7,12,13,14,15,16],by decide⟩

def matrixPrefix : Routine 19 := sequence (readListHeader 4 matrixHeaderRoles)
  (sequence (ofProgram (ListPrograms.copyProgram 18 20 18 4))
    (sequence dimensionGuard (sequence (clear 18)
      (sequence (forEach 20 rowPrefix) (ofProgram (ListPrograms.reverseProgram 19 19 2))))))

def matrixShape (width : Nat) (rows : List (List Nat)) : Bool :=
  decide (width=rows.length) && rowLengths width rows

def matrixPrefixStore (store : Store 19) (accepted : Bool) (tail : List Bool)
    (rows : List (List Nat)) (suffix : List Bool) : Store 19 :=
  Function.update (Function.update (Function.update store 17 suffix)
    1 ((accepted && matrixShape (store 0).length rows)::tail)) 2 (adjacencyBits rows)

theorem adjacencyBits_length_le (rows : List (List Nat)) :
    (adjacencyBits rows).length ≤ (Encoding.sequence (Encoding.list Encoding.natural) rows).length := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    have count := VerifiedParser.sequence_count_le (codec:=Encoding.natural)
      (by intro value;rw [Encoding.natural_length];omega) row
    change (row.map (fun value=>decide (0<value))++adjacencyBits rows).length ≤ _
    change _ ≤ ((Encoding.natural.encode row.length++Encoding.sequence Encoding.natural row)++
      Encoding.sequence (Encoding.list Encoding.natural) rows).length
    simp only [List.length_append,List.length_map]
    omega

/-- Build the actual row-major adjacency vector and test every dimension.
The number of matrix entries is read from canonical headers, never assumed
equal to the population. Wrong shapes still terminate and set status false. -/
theorem matrixPrefix_executes (store : Store 19) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀r:Fin 21,r.val<17 → r≠0 → r≠1 → store r=[])
    (e18 : store 18=[]) (e19 : store 19=[]) (e20 : store 20=[])
    (rows : List (List Nat)) (suffix : List Bool)
    (input : store 17=(Encoding.list (Encoding.list Encoding.natural)).encode rows++suffix) :
    ∃time ≤ 4000*((store 17).length+(store 0).length+1)^4,
      Executes matrixPrefix store time (matrixPrefixStore store accepted tail rows suffix) := by
  have positive (row:List Nat) : 0<((Encoding.list Encoding.natural).encode row).length := by
    change 0<(Encoding.natural.encode row.length++Encoding.sequence Encoding.natural row).length
    rw [List.length_append,Encoding.natural_length];omega
  have headerWork (i:Fin 17) (member:i∈({2,3,4,5,8,11,12,13,14,15,16}:Finset (Fin 17))) :
      store (matrixHeaderRoles i)=[] := by
    fin_cases i
    all_goals simp only [Finset.mem_insert,Finset.mem_singleton] at member
    all_goals first | contradiction | simp [matrixHeaderRoles,work,e20]
  obtain ⟨headerTime,headerBound,headerRun⟩ := readListHeader_canonical 4 matrixHeaderRoles store accepted tail
    status headerWork (Encoding.list Encoding.natural) positive rows suffix input
  let ready := Function.update (Function.update store 17 (Encoding.sequence (Encoding.list Encoding.natural) rows++suffix))
    20 (List.replicate rows.length true)
  have copying := copy_executes 18 (20:Fin 21) 18 4 (by decide) (by decide) (by decide)
    ready (by simp [ready,work])
  rw [show ready 20=List.replicate rows.length true by simp [ready],
    show ready 18=[] by simp [ready,e18],List.append_nil,List.length_replicate] at copying
  let copied := Function.update ready 18 (List.replicate rows.length true)
  obtain ⟨guardTime,guardBound,guardRun⟩ := dimensionGuard_executes copied accepted tail
    (by simp [copied,ready,status]) (by simp [copied,ready,work]) (by simp [copied,ready,work])
    (by simp [copied,ready,work]) (by simp [copied])
  rw [show copied 0=store 0 by simp [copied,ready],show (copied 18).length=rows.length by simp [copied]] at guardBound guardRun
  let checked := Function.update copied 1 ((accepted && decide ((store 0).length=rows.length))::tail)
  have clearing := clear_executes (18:Fin 21) checked
  rw [show checked 18=List.replicate rows.length true by simp [checked,copied],List.length_replicate] at clearing
  let cleaned := Function.update checked 18 []
  obtain ⟨loopTime,loopBound,loopRun⟩ := rows_executes cleaned (accepted && decide ((store 0).length=rows.length)) tail
    (by simp [cleaned,checked])
    (by intro r h n0 n1
        have n17:r≠17:=by intro eq;subst r;norm_num at h
        have n18:r≠18:=by intro eq;subst r;norm_num at h
        have n20:r≠20:=by intro eq;subst r;norm_num at h
        simpa [cleaned,checked,copied,ready,n1,n17,n18,n20] using work r h n0 n1)
    (by simp [cleaned]) rows suffix (by simp [cleaned,checked,copied,ready]) (by simp [cleaned,checked,copied,ready])
  let scanned := rowsStore cleaned (accepted && decide ((store 0).length=rows.length)) tail rows suffix
  have reversing := reverse_executes 19 (19:Fin 21) 2 (by decide) scanned
  have output : scanned 19=(adjacencyBits rows).reverse := by simp [scanned,rowsStore,cleaned,checked,copied,ready,e19]
  have empty : scanned 2=[] := by simp [scanned,rowsStore,cleaned,checked,copied,ready,work]
  rw [output,empty,List.append_nil,List.reverse_reverse,List.length_reverse] at reversing
  have final : Function.update (Function.update scanned 19 []) 2 (adjacencyBits rows)=
      matrixPrefixStore store accepted tail rows suffix := by
    funext r
    fin_cases r <;> simp [scanned,rowsStore,cleaned,checked,copied,ready,matrixPrefixStore,matrixShape,
      Bool.and_assoc,work,e18,e19,e20]
  rw [final] at reversing
  have shorter : (cleaned 17).length ≤ (store 17).length := by
    rw [input]
    change (Encoding.sequence (Encoding.list Encoding.natural) rows++suffix).length ≤
      ((Encoding.natural.encode rows.length++Encoding.sequence (Encoding.list Encoding.natural) rows)++suffix).length
    simp only [List.length_append];omega
  have countBound : rows.length ≤ (store 17).length := by
    have count := VerifiedParser.sequence_count_le positive rows
    rw [input]
    change rows.length ≤ ((Encoding.natural.encode rows.length++Encoding.sequence (Encoding.list Encoding.natural) rows)++suffix).length
    simp only [List.length_append];omega
  have bitsBound : (adjacencyBits rows).length ≤ (store 17).length := by
    have count := adjacencyBits_length_le rows
    rw [input]
    change _ ≤ ((Encoding.natural.encode rows.length++Encoding.sequence (Encoding.list Encoding.natural) rows)++suffix).length
    simp only [List.length_append];omega
  let S := (store 17).length+(store 0).length+1
  have base : S=(store 17).length+(store 0).length+1 := rfl
  have pos : 1≤S := by omega
  have headerLimit : headerTime ≤ 1820*S^3 := by
    apply headerBound.trans
    change 1820*((store 17).length+1)^3 ≤ _
    gcongr;omega
  have width : cleaned 0=store 0 := by simp [cleaned,checked,copied,ready]
  rw [width] at loopBound
  have loopLimit : loopTime ≤ S*(1900*S^3+2)+1 := by
    apply loopBound.trans;gcongr <;> omega
  have linear : S≤S^4 := Nat.le_self_pow (by decide) _
  have cubic : S^3≤S^4 := Nat.pow_le_pow_right pos (by decide)
  have one : 1≤S^4 := Nat.one_le_pow _ _ pos
  refine ⟨_,?_,headerRun.sequence (copying.sequence (guardRun.sequence (clearing.sequence (loopRun.sequence reversing))))⟩
  change _ ≤ 4000*S^4
  nlinarith

end Counting.StackMachine.NetworkRecognition
