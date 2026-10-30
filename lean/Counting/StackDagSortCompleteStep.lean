import Counting.StackDagSortInsertionBounds
import Counting.StackDagSortQuery

namespace Counting.StackMachine.DagUpdate.Sort
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

/-- The outer sort owns the unread stream, its counter, and the number of
already inserted records. The insertion primitive keeps its original roles. -/
def queryReaderRoles : Fin 20 ↪ Fin 96 :=
  ⟨![92,81,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,82,78,79],by decide⟩

def readQuery : Routine 94 := relocate readRecord queryReaderRoles

def SortEmpty (store : Store 94) : Prop :=
  ∀ r : Fin 96,r.val≤14 ∨ (40≤r.val ∧ r.val≤44) ∨ (49≤r.val ∧ r.val≤51) ∨
    r∈({64,65,66,67,82,83,84,86,87,88,89,90,91}:Finset (Fin 96)) → store r=[]

theorem readQuery_executes (store : Store 94) (query : Record) (suffix : List Bool)
    (source : store 92=recordCodec.encode query++suffix) (status : store 81=[true])
    (empty : SortEmpty store) :
    ∃time≤2100*((store 92).length+1)^3,
      Executes readQuery store time
        (Function.update (Function.update store 92 suffix) 82 (recordCodec.encode query)) := by
  let localStore : Store 18 := store ∘ queryReaderRoles
  obtain ⟨time,bound,run⟩:=readRecord_executes localStore query suffix true [] source status (by
    intro r lower upper
    fin_cases r <;> simp_all [localStore,queryReaderRoles,SortEmpty])
  refine ⟨time,bound,?_⟩
  apply relocate_executes_frame readRecord queryReaderRoles store _ localStore
    (Function.update (Function.update localStore 0 suffix) 17 (recordCodec.encode query)) time rfl _ _ run
  · intro r
    fin_cases r <;> simp [localStore,queryReaderRoles]
  · intro r outside
    have n92:r≠92:=fun same=>outside 0 (by simpa [queryReaderRoles] using same.symm)
    have n82:r≠82:=fun same=>outside 17 (by simpa [queryReaderRoles] using same.symm)
    simp [n92,n82]

def insertQuery : Routine 94 := sequence prepareQuery
  (sequence (ofProgram (ListPrograms.copyProgram 93 94 90 89))
    (sequence (pushBit 84 false) insertCore))

def insertedQuery (store : Store 94) (query : Record) (records : List Record) : Store 94 :=
  Function.update (Function.update (Function.update store 80 []) 64 (Encoding.node.encode query.2))
    91 (Encoding.sequence recordCodec (List.orderedInsert (fun a b=>recordLE a b=true) query records))

theorem insertQuery_executes (store : Store 94) (query : Record) (records : List Record)
    (source : store 80=Encoding.sequence recordCodec records)
    (queryAt : store 82=recordCodec.encode query) (status : store 81=[true])
    (counter : store 94=List.replicate records.length true)
    (empty : ∀ r : Fin 96,r.val≤14 ∨ (40≤r.val ∧ r.val≤44) ∨ (49≤r.val ∧ r.val≤51) ∨
      r∈({64,65,66,67,83,84,86,87,88,89,90,91}:Finset (Fin 96)) → store r=[]) :
    ∃time≤22000*((store 80).length+(store 82).length+1)^4,
      Executes insertQuery store time (insertedQuery store query records) := by
  have preparing:=prepareQuery_executes store query queryAt
    (empty 64 (by simp)) (empty 87 (by simp)) (empty 89 (by simp))
  let prepared:=Function.update store 64 (Encoding.node.encode query.2)
  have copying:=copy_executes 93 (94:Fin 96) 90 89 (by decide) (by decide) (by decide)
    prepared (by simp [prepared,empty])
  have countAt:prepared 94=List.replicate records.length true:=by simp [prepared,counter]
  have targetAt:prepared 90=[]:=by simp [prepared,empty]
  rw [countAt,targetAt,List.append_nil,List.length_replicate] at copying
  let counted:=Function.update prepared 90 (List.replicate records.length true)
  have pushing:=pushBit_executes (84:Fin 96) false counted
  have flagAt:counted 84=[]:=by simp [counted,prepared,empty]
  rw [flagAt] at pushing
  let ready:=Function.update counted 84 [false]
  obtain ⟨time,bound,run⟩:=insertCore_executes_polynomial ready query records []
    (by simp [ready,counted,prepared,source]) (by simp [ready,counted,prepared])
    (by simp [ready,counted,prepared,queryAt]) (by simp [ready,counted,prepared,status])
    (by simp [ready]) (by simp [ready,counted])
    (by simp [ready,counted,prepared,empty]) (by
      intro r allowed
      fin_cases r <;> simp_all [ready,counted,prepared])
  have final:insertCoreResult ready query records []=insertedQuery store query records:=by
    funext r
    by_cases r64:r=64 <;> by_cases r80:r=80 <;> by_cases r84:r=84 <;>
      by_cases r90:r=90 <;> by_cases r91:r=91 <;>
      simp [insertCoreResult,insertedQuery,ready,counted,prepared,r64,r80,r84,r90,r91,empty]
  rw [final] at run
  have sameSource:ready 80=store 80:=by simp [ready,counted,prepared]
  have sameQuery:ready 82=store 82:=by simp [ready,counted,prepared]
  rw [sameSource,sameQuery] at bound
  refine ⟨_,?_,preparing.sequence (copying.sequence (pushing.sequence run))⟩
  have countBound:records.length≤(store 80).length:=by rw [source];exact records_length_le_sequence _
  have indexBound:query.1.bits.length≤(store 82).length:=by
    rw [queryAt]
    simp only [recordCodec,Encoding.product,List.length_append,Encoding.natural_length,Encoding.bits_length]
    omega
  rw [←queryAt]
  have linear:((store 80).length+(store 82).length+1)≤
      ((store 80).length+(store 82).length+1)^4:=Nat.le_self_pow (by decide) _
  have one:1≤((store 80).length+(store 82).length+1)^4:=Nat.one_le_pow _ _ (by omega)
  omega

def commitSorted : Routine 94 := sequence (move 93 91 80 89)
  (sequence (clear 64) (sequence (clear 82) (pushBit 94 true)))

def sortStep : Routine 94 := sequence readQuery (sequence insertQuery commitSorted)

def sortStepResult (store : Store 94) (query : Record) (records : List Record)
    (suffix : List Bool) : Store 94 :=
  Function.update (Function.update (Function.update store 92 suffix)
    80 (Encoding.sequence recordCodec (List.orderedInsert (fun a b=>recordLE a b=true) query records)))
    94 (true::store 94)

theorem sortStep_executes (store : Store 94) (query : Record) (records : List Record) (suffix : List Bool)
    (input : store 92=recordCodec.encode query++suffix)
    (sorted : store 80=Encoding.sequence recordCodec records)
    (status : store 81=[true]) (counter : store 94=List.replicate records.length true)
    (empty : SortEmpty store) :
    ∃time≤25000*((store 92).length+(store 80).length+1)^4,
      Executes sortStep store time (sortStepResult store query records suffix) := by
  obtain ⟨readTime,readBound,reading⟩:=readQuery_executes store query suffix input status empty
  let parsed:=Function.update (Function.update store 92 suffix) 82 (recordCodec.encode query)
  obtain ⟨insertTime,insertBound,inserting⟩:=insertQuery_executes parsed query records
    (by simp [parsed,sorted]) (by simp [parsed]) (by simp [parsed,status])
    (by simp [parsed,counter]) (by
      intro r allowed
      fin_cases r <;> simp_all [parsed,SortEmpty])
  let inserted:=insertedQuery parsed query records
  let result:=Encoding.sequence recordCodec (List.orderedInsert (fun a b=>recordLE a b=true) query records)
  have moving:=move_executes 93 (91:Fin 96) 80 89 (by decide) (by decide) (by decide)
    inserted (by simp [inserted,insertedQuery,parsed,empty 89 (by simp)])
  have sourceAt:inserted 91=result:=by simp [inserted,insertedQuery,result]
  have dest:inserted 80=[]:=by simp [inserted,insertedQuery]
  rw [sourceAt,dest,List.append_nil] at moving
  let moved:=Function.update (Function.update inserted 80 result) 91 []
  have clearNode:=clear_executes (64:Fin 96) moved
  have nodeAt:moved 64=Encoding.node.encode query.2:=by simp [moved,inserted,insertedQuery]
  rw [nodeAt] at clearNode
  let noNode:=Function.update moved 64 []
  have clearRecord:=clear_executes (82:Fin 96) noNode
  have recordAt:noNode 82=recordCodec.encode query:=by simp [noNode,moved,inserted,insertedQuery,parsed]
  rw [recordAt] at clearRecord
  let cleaned:=Function.update noNode 82 []
  have increment:=pushBit_executes (94:Fin 96) true cleaned
  have countAt:cleaned 94=store 94:=by simp [cleaned,noNode,moved,inserted,insertedQuery,parsed]
  rw [countAt] at increment
  have final:Function.update cleaned 94 (true::store 94)=sortStepResult store query records suffix:=by
    funext r
    by_cases r64:r=64 <;> by_cases r80:r=80 <;> by_cases r82:r=82 <;>
      by_cases r91:r=91 <;> by_cases r92:r=92 <;> by_cases r94:r=94 <;>
      simp_all [cleaned,noNode,moved,inserted,insertedQuery,parsed,sortStepResult,result,SortEmpty]
  rw [final] at increment
  refine ⟨_,?_,reading.sequence (inserting.sequence
    (moving.sequence (clearNode.sequence (clearRecord.sequence increment))))⟩
  have queryBound:(recordCodec.encode query).length≤(store 92).length:=by rw [input,List.length_append];omega
  have nodeBound:(Encoding.node.encode query.2).length≤(recordCodec.encode query).length:=by
    simp only [recordCodec,Encoding.product,List.length_append];omega
  have resultLength:result.length=(recordCodec.encode query).length+(store 80).length:=by
    rw [sorted];exact orderedInsert_encoded_length _ _
  have parsed80:parsed 80=store 80:=by simp [parsed]
  have parsed82:parsed 82=recordCodec.encode query:=by simp [parsed]
  rw [parsed80,parsed82] at insertBound
  let K:=(store 92).length+(store 80).length+1
  have positive:1≤K:=by dsimp [K];omega
  have rp:((store 92).length+1)^3≤K^4:=
    (Nat.pow_le_pow_left (by dsimp [K];omega) 3).trans (Nat.pow_le_pow_right positive (by decide))
  have ip:((store 80).length+(recordCodec.encode query).length+1)^4≤K^4:=by
    apply Nat.pow_le_pow_left;dsimp [K];omega
  have linear:K≤K^4:=Nat.le_self_pow (by decide) _
  have one:1≤K^4:=one_le_pow₀ positive
  have first:=readBound.trans (Nat.mul_le_mul_left 2100 rp)
  have second:=insertBound.trans (Nat.mul_le_mul_left 22000 ip)
  change _≤25000*K^4
  dsimp only [K] at *
  omega

end Counting.StackMachine.DagUpdate.Sort
