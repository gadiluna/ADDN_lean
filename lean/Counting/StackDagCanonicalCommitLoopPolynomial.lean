import Counting.StackDagCanonicalCommitLoopBounds

namespace Counting.StackMachine.DagUpdate.Canonical
open Executable Routine
set_option maxHeartbeats 1600000

theorem commitFold_mapping_size (state : CanonicalState) (records : List Sort.Record) :
    (records.foldl commitRecord state).2.size=state.2.size := by
  induction records generalizing state with
  | nil => rfl
  | cons record records ih =>
    simpa only [List.foldl_cons,commitRecord_mapping_size] using ih (commitRecord state record)

def commitStepCoefficient : Nat := 1000000*10^4

theorem commitStepBudget_prefix (state : CanonicalState) (records visited rest : List Sort.Record)
    (record : Sort.Record) (suffix : List Bool) (partition : visited++record::rest=records)
    (inside : record.1 < state.2.size) :
    commitStepBudget (visited.foldl commitRecord state) record
      (Encoding.sequence Sort.recordCodec (record::rest)++suffix).length ≤
      commitStepCoefficient*(commitInputSize state records suffix)^8 := by
  let K := commitInputSize state records suffix
  let before := visited.foldl commitRecord state
  let cap := 10*K^2
  have positive : 1 ≤ K := by dsimp [K,commitInputSize];omega
  have linear : K ≤ K^2 := Nat.le_self_pow (by decide) _
  have old := commitPrefix_encoded_bounds state records visited (record::rest) suffix partition
  have next := commitPrefix_encoded_bounds state records (visited++[record]) rest suffix
    (by simpa only [List.append_assoc,List.singleton_append] using partition)
  have nextState : (visited++[record]).foldl commitRecord state=commitRecord before record := by
    simp [before]
  dsimp only at old next
  rw [nextState] at next
  have member : record∈records := by rw [←partition];simp
  have recordBound : (Sort.recordCodec.encode record).length ≤ K := by
    have bound := Encoding.array_member_length_le Sort.recordCodec records.toArray record (by simpa using member)
    simp only [Encoding.array,Encoding.transport] at bound
    dsimp [K,commitInputSize]
    omega
  have sourceBound : (Encoding.sequence Sort.recordCodec (record::rest)++suffix).length ≤ K := by
    dsimp [K,commitInputSize]
    rw [←partition]
    simp only [Encoding.list,List.length_append,Encoding.sequence_length,List.map_append,List.sum_append]
    omega
  have sameSize : before.2.size=state.2.size := by
    exact commitFold_mapping_size state visited
  have result := commitStepBudget_cap before record
    (Encoding.sequence Sort.recordCodec (record::rest)++suffix).length cap (by dsimp [cap];omega)
    (by rw [sameSize];exact inside) old.2 old.1 (by dsimp [cap];omega) next.1 (by dsimp [cap];omega)
  refine result.trans_eq ?_
  dsimp only [cap,commitStepCoefficient]
  ring

theorem commitLoopBudget_suffix_bound (state : CanonicalState) (records visited rest : List Sort.Record)
    (suffix : List Bool) (partition : visited++rest=records)
    (inside : ∀ record∈records,record.1 < state.2.size) :
    commitLoopBudget (visited.foldl commitRecord state) rest suffix ≤
      rest.length*(commitStepCoefficient*(commitInputSize state records suffix)^8+2)+1 := by
  induction rest generalizing visited with
  | nil => simp [commitLoopBudget]
  | cons record rest ih =>
    have member : record∈records := by rw [←partition];simp
    have first := commitStepBudget_prefix state records visited rest record suffix partition (inside record member)
    have tail := ih (visited++[record]) (by simpa only [List.append_assoc,List.singleton_append] using partition)
    simp only [List.foldl_append,List.foldl_cons,List.foldl_nil] at tail
    simp only [commitLoopBudget,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem commitLoopBudget_polynomial (state : CanonicalState) (records : List Sort.Record) (suffix : List Bool)
    (inside : ∀ record∈records,record.1 < state.2.size) :
    commitLoopBudget state records suffix ≤ (commitStepCoefficient+3)*(commitInputSize state records suffix)^9 := by
  let K := commitInputSize state records suffix
  have result := commitLoopBudget_suffix_bound state records [] records suffix rfl inside
  simp only [List.foldl_nil] at result
  have count : records.length ≤ ((Encoding.list Sort.recordCodec).encode records).length := by
    simpa only [Encoding.array,Encoding.transport,List.toList_toArray,List.size_toArray] using
      Encoding.array_size_le_length Sort.recordCodec records.toArray (fun record _=>record_positive_length record)
  have countBound : records.length ≤ K := by dsimp [K,commitInputSize];omega
  have positive : 1 ≤ K := by dsimp [K,commitInputSize];omega
  have multiplied := Nat.mul_le_mul_right (commitStepCoefficient*K^8+2) countBound
  have linear : K ≤ K^9 := Nat.le_self_pow (by decide) _
  have one : 1 ≤ K^9 := one_le_pow₀ positive
  have power : K*K^8=K^9 := by ring
  change _ ≤ (commitStepCoefficient+3)*K^9
  change commitLoopBudget state records suffix ≤ records.length*(commitStepCoefficient*K^8+2)+1 at result
  nlinarith only [result,multiplied,linear,one,power]

def commitRecordsCoefficient : Nat := commitStepCoefficient+1824

/-- The canonical insertion loop has a polynomial cost in the compact
serialized pool, mapping and indexed signatures, without expanding counts. -/
theorem commitRecords_polynomial (store : Store 94) (state : CanonicalState)
    (records : List Sort.Record) (suffix : List Bool)
    (inside : ∀ record∈records,record.1 < state.2.size)
    (source : store 92=(Encoding.list Sort.recordCodec).encode records++suffix)
    (mappingAt : store 1=(Encoding.array Encoding.natural).encode state.2)
    (poolAt : store 64=(Encoding.array Encoding.node).encode state.1)
    (status : store 81=[true]) (counterEmpty : store 93=[]) (empty : CommitScratch store) :
    ∃ time ≤ commitRecordsCoefficient*((store 64).length+(store 1).length+(store 92).length+1)^9,
      Executes commitRecords store time (commitLoopResult store state records suffix) := by
  obtain ⟨time,bound,run⟩ := commitRecords_executes store state records suffix inside source mappingAt poolAt status counterEmpty empty
  let K := commitInputSize state records suffix
  have loop := commitLoopBudget_polynomial state records suffix inside
  have sourceBound : (store 92).length+1 ≤ K := by rw [source,List.length_append];dsimp [K,commitInputSize];omega
  have positive : 1 ≤ K := by dsimp [K,commitInputSize];omega
  have power := (Nat.pow_le_pow_left sourceBound 3).trans (Nat.pow_le_pow_right positive (by decide : 3 ≤ 9))
  have one : 1 ≤ K^9 := one_le_pow₀ positive
  have input : (store 64).length+(store 1).length+(store 92).length+1=K := by
    rw [poolAt,mappingAt,source,List.length_append]
    dsimp [K,commitInputSize];omega
  refine ⟨time,?_,run⟩
  rw [input]
  change time ≤ (commitStepCoefficient+1824)*K^9
  change commitLoopBudget state records suffix ≤ (commitStepCoefficient+3)*K^9 at loop
  nlinarith only [bound,loop,power,one]

end Counting.StackMachine.DagUpdate.Canonical
