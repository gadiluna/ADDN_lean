import Counting.NetworkRecognitionArcLoop
import Counting.NetworkRecognitionDimensions
import Counting.StackEncodingListReadHeader
import Counting.StackEncodingParserMany

namespace Counting.StackMachine.NetworkRecognition
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

def rowHeaderRoles : FullListWorkspace 4 := ⟨![17,1,3,4,18,5,8,9,6,10,11,7,12,13,14,15,16],by decide⟩

def rowPrefix : Routine 19 := sequence (readListHeader 4 rowHeaderRoles)
  (sequence dimensionGuard (forEach 18 arcItem))

def rowPrefixStore (store : Store 19) (accepted : Bool) (tail : List Bool)
    (values : List Nat) (suffix : List Bool) : Store 19 :=
  Function.update (Function.update (Function.update store 17 suffix)
    1 ((accepted && decide ((store 0).length=values.length))::tail))
    19 ((values.map (fun value=>decide (0<value))).reverse++store 19)

/-- Check the actual row length and read every binary multiplicity. Even a
wrong row length is processed and rejected; no shape premise is assumed. -/
theorem rowPrefix_executes (store : Store 19) (accepted : Bool) (tail : List Bool)
    (status : store 1=accepted::tail)
    (work : ∀r:Fin 21,r.val<17 → r≠0 → r≠1 → store r=[])
    (e18 : store 18=[]) (values : List Nat) (suffix : List Bool)
    (input : store 17=(Encoding.list Encoding.natural).encode values++suffix) :
    ∃time ≤ 1900*((store 17).length+(store 0).length+1)^3,
      Executes rowPrefix store time (rowPrefixStore store accepted tail values suffix) := by
  have positive (value:Nat) : 0<(Encoding.natural.encode value).length := by
    rw [Encoding.natural_length];omega
  have headerWork (i:Fin 17) (member:i∈({2,3,4,5,8,11,12,13,14,15,16}:Finset (Fin 17))) :
      store (rowHeaderRoles i)=[] := by
    fin_cases i
    all_goals simp only [Finset.mem_insert,Finset.mem_singleton] at member
    all_goals first | contradiction | simp [rowHeaderRoles,work,e18]
  obtain ⟨headerTime,headerBound,headerRun⟩ := readListHeader_canonical 4 rowHeaderRoles store accepted tail
    status headerWork Encoding.natural positive values suffix input
  let ready := Function.update (Function.update store 17 (Encoding.sequence Encoding.natural values++suffix))
    18 (List.replicate values.length true)
  obtain ⟨guardTime,guardBound,guardRun⟩ := dimensionGuard_executes ready accepted tail
    (by simp [ready,status]) (by simp [ready,work]) (by simp [ready,work]) (by simp [ready,work])
    (by simp [ready])
  have widthAt : ready 0=store 0 := by simp [ready]
  have countAt : (ready 18).length=values.length := by simp [ready]
  rw [widthAt,countAt] at guardBound guardRun
  let checked := Function.update ready 1 ((accepted && decide ((store 0).length=values.length))::tail)
  obtain ⟨loopTime,loopBound,loopRun⟩ := arcValues_executes checked values suffix
    (by simp [checked,ready]) (by simp [checked,ready]) (by simp [checked,ready,work])
    (by simp [checked,ready,work])
  have final : arcValuesStore checked values suffix=rowPrefixStore store accepted tail values suffix := by
    funext r
    by_cases r1:r=1 <;> by_cases r17:r=17 <;> by_cases r18:r=18 <;> by_cases r19:r=19 <;>
      simp [arcValuesStore,checked,ready,rowPrefixStore,r1,r17,r18,r19,e18]
  rw [final] at loopRun
  have shorter : (checked 17).length ≤ (store 17).length := by
    rw [input]
    change (Encoding.sequence Encoding.natural values++suffix).length ≤
      ((Encoding.natural.encode values.length++Encoding.sequence Encoding.natural values)++suffix).length
    simp only [List.length_append]
    omega
  have countBound : values.length ≤ (store 17).length := by
    have count := VerifiedParser.sequence_count_le positive values
    rw [input]
    change values.length ≤ ((Encoding.natural.encode values.length++Encoding.sequence Encoding.natural values)++suffix).length
    simp only [List.length_append]
    omega
  let S := (store 17).length+(store 0).length+1
  have base : S=(store 17).length+(store 0).length+1 := rfl
  have positiveS : 1≤S := by omega
  have headLimit : headerTime ≤ 1820*S^3 := by
    apply headerBound.trans
    change 1820*((store 17).length+1)^3 ≤ _
    gcongr
    omega
  have loopLimit : loopTime ≤ S*(6*S+13)+1 := by
    apply loopBound.trans
    gcongr <;> omega
  have linear : S≤S^3 := Nat.le_self_pow (by decide) _
  have square : S^2≤S^3 := Nat.pow_le_pow_right positiveS (by decide)
  have one : 1≤S^3 := Nat.one_le_pow _ _ positiveS
  refine ⟨headerTime+1+(guardTime+1+loopTime),?_,headerRun.sequence (guardRun.sequence loopRun)⟩
  change _ ≤ 1900*S^3
  nlinarith

end Counting.StackMachine.NetworkRecognition
