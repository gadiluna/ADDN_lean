import Counting.StackDagSortCompleteLoop
import Counting.StackEncodingListReadHeader
import Counting.StackEmitNatural
import Counting.StackRoutineClean
import Counting.DagCanonicalRecordsSpec

namespace Counting.StackMachine.DagUpdate.Sort
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

def sortHeaderRoles : FullListWorkspace 79 :=
  ⟨![92,81,0,1,93,2,3,4,5,6,7,8,9,10,11,12,13],by decide⟩

def sortHeader : Routine 94 := readListHeader 79 sortHeaderRoles

theorem sortHeader_executes (store : Store 94) (records : List Record) (suffix : List Bool)
    (source : store 92=(Encoding.list recordCodec).encode records++suffix)
    (status : store 81=[true]) (e93:store 93=[])
    (empty : ∀r:Fin 96,r.val≤13 → store r=[]) :
    ∃time≤1820*((store 92).length+1)^3,
      Executes sortHeader store time
        (Function.update (Function.update store 92 (Encoding.sequence recordCodec records++suffix))
          93 (List.replicate records.length true)) := by
  apply readListHeader_canonical 79 sortHeaderRoles store true [] status _ recordCodec _ records suffix source
  · intro r member
    fin_cases r <;> simp_all [sortHeaderRoles]
  · intro value
    simp only [recordCodec,Encoding.product,List.length_append,Encoding.natural_length]
    omega

def sortInput (records : List Record) : List Bool := (Encoding.list recordCodec).encode records

/-- The level builder can prepend each indexed signature as it scans its
original indices. This sorter consumes that reversed record order. -/
def sortOutput (records : List Record) : List Bool :=
  (Encoding.list recordCodec).encode (insertFold records [])

def prepareSort : Routine 94 := sequence (move 93 0 92 89)
  (sequence (pushBit 81 true) sortHeader)

def preparedSort (records : List Record) : Store 94 :=
  Function.update (Function.update (Function.update (fun _=>[]) 81 [true])
    92 (Encoding.sequence recordCodec records)) 93 (List.replicate records.length true)

theorem prepareSort_executes (records : List Record) :
    ∃time≤1900*((sortInput records).length+1)^3,
      Executes prepareSort (inputStore 94 (sortInput records)) time (preparedSort records) := by
  let start:=inputStore 94 (sortInput records)
  have moving:=move_executes 93 (0:Fin 96) 92 89 (by decide) (by decide) (by decide) start rfl
  have sourceAt:start 0=sortInput records:=rfl
  have targetAt:start 92=[]:=rfl
  rw [sourceAt,targetAt,List.append_nil] at moving
  let moved:=Function.update (Function.update start 92 (sortInput records)) 0 []
  have pushing:=pushBit_executes (81:Fin 96) true moved
  have statusAt:moved 81=[]:=by simp [moved,start,inputStore]
  rw [statusAt] at pushing
  let ready:=Function.update moved 81 [true]
  obtain ⟨headerTime,headerBound,reading⟩:=sortHeader_executes ready records []
    (by simp [ready,moved,sortInput]) (by simp [ready])
    (by simp [ready,moved,start,inputStore]) (by
      intro r small
      have n81:r≠81:=by intro eq;subst r;norm_num at small
      have n92:r≠92:=by intro eq;subst r;norm_num at small
      by_cases zero:r=0
      · subst r;simp [ready,moved]
      · simp [ready,moved,start,inputStore,n81,n92,zero])
  have final:Function.update (Function.update ready 92 (Encoding.sequence recordCodec records++[]))
      93 (List.replicate records.length true)=preparedSort records:=by
    funext r
    by_cases r0:r=0 <;> by_cases r81:r=81 <;> by_cases r92:r=92 <;> by_cases r93:r=93 <;>
      simp [preparedSort,ready,moved,start,inputStore,r0,r81,r92,r93]
  rw [final] at reading
  have inputAt:ready 92=sortInput records:=by simp [ready,moved]
  rw [inputAt] at headerBound
  refine ⟨_,?_,moving.sequence (pushing.sequence reading)⟩
  have linear:(sortInput records).length+1≤((sortInput records).length+1)^3:=Nat.le_self_pow (by decide) _
  omega

def sortOutputHeaderRoles : PowerWorkspace 91 := ⟨![94,80,0,2,3],by decide⟩

def finishSort : Routine 94 := sequence (emitNatural 91 sortOutputHeaderRoles)
  (sequence (move 93 80 1 89) (sequence (clear 81) (clear 94)))

theorem finishSort_executes (records : List Record) :
    ∃time≤100*((sortInput records).length+1)^2,
      Executes finishSort (sortLoopResult (preparedSort records) records [] []) time
        (outputStore 94 (sortOutput records)) := by
  let source:=sortLoopResult (preparedSort records) records [] []
  have countAt:source 94=List.replicate records.length true:=by simp [source,sortLoopResult]
  have payloadAt:source 80=Encoding.sequence recordCodec (insertFold records []):=by
    simp [source,sortLoopResult]
  obtain ⟨headerTime,headerBound,header⟩:=emitNatural_executes 91 sortOutputHeaderRoles source
    (by simp [sortOutputHeaderRoles,source,sortLoopResult,preparedSort])
    (by simp [sortOutputHeaderRoles,source,sortLoopResult,preparedSort])
    (by simp [sortOutputHeaderRoles,source,sortLoopResult,preparedSort])
  have countLength:(source (sortOutputHeaderRoles 0)).length=records.length:=by
    simp [sortOutputHeaderRoles,countAt]
  have payload:source (sortOutputHeaderRoles 1)=Encoding.sequence recordCodec (insertFold records []):=payloadAt
  rw [countLength,payload] at header
  rw [countLength] at headerBound
  have headerOutput:Encoding.natural.encode records.length++Encoding.sequence recordCodec (insertFold records [])=
      sortOutput records:=by simp [sortOutput,Encoding.list,insertFold_length]
  rw [headerOutput] at header
  let framed:=Function.update source 80 (sortOutput records)
  have moving:=move_executes 93 (80:Fin 96) 1 89 (by decide) (by decide) (by decide) framed
    (by simp [framed,source,sortLoopResult,preparedSort])
  have fromAt:framed 80=sortOutput records:=by simp [framed]
  have toAt:framed 1=[]:=by simp [framed,source,sortLoopResult,preparedSort]
  rw [fromAt,toAt,List.append_nil] at moving
  let moved:=Function.update (Function.update framed 1 (sortOutput records)) 80 []
  have clearStatus:=clear_executes (81:Fin 96) moved
  have statusAt:moved 81=[true]:=by simp [moved,framed,source,sortLoopResult,preparedSort]
  rw [statusAt,List.length_singleton] at clearStatus
  let cleaned:=Function.update moved 81 []
  have clearCount:=clear_executes (94:Fin 96) cleaned
  have countAt':cleaned 94=List.replicate records.length true:=by simp [cleaned,moved,framed,countAt]
  rw [countAt',List.length_replicate] at clearCount
  have final:Function.update cleaned 94 []=outputStore 94 (sortOutput records):=by
    funext r
    by_cases r1:r=1 <;> by_cases r80:r=80 <;> by_cases r81:r=81 <;>
      by_cases r92:r=92 <;> by_cases r93:r=93 <;> by_cases r94:r=94 <;>
      simp [cleaned,moved,framed,source,sortLoopResult,preparedSort,outputStore,r1,r80,r81,r92,r93,r94]
  rw [final] at clearCount
  refine ⟨_,?_,header.sequence (moving.sequence (clearStatus.sequence clearCount))⟩
  have outLength:(sortOutput records).length=(sortInput records).length:=by
    simp [sortOutput,sortInput,Encoding.list,insertFold_length,List.length_append,
      insertFold_encoded_length,Encoding.sequence]
  have countBound:records.length≤(sortInput records).length:=by
    have bound:=records_length_le_sequence records
    simp only [sortInput,Encoding.list,List.length_append]
    omega
  rw [outLength]
  have power:(records.length+1)^2≤((sortInput records).length+1)^2:=by gcongr
  have linear:(sortInput records).length+1≤((sortInput records).length+1)^2:=Nat.le_self_pow (by decide) _
  have h:=headerBound.trans (Nat.mul_le_mul_left 20 power)
  omega

def completeSort : Routine 94 := sequence prepareSort (sequence sortLoop finishSort)

theorem completeSort_executes (records : List Record) :
    ∃time≤30000*((sortInput records).length+1)^5,
      Executes completeSort (inputStore 94 (sortInput records)) time
        (outputStore 94 (sortOutput records)) := by
  obtain ⟨prepareTime,prepareBound,preparing⟩:=prepareSort_executes records
  have sourceLength:(Encoding.sequence recordCodec records).length≤(sortInput records).length:=by
    simp only [sortInput,Encoding.list,List.length_append];omega
  obtain ⟨bodyTime,bodyBound,body⟩:=sortLoop_executes (preparedSort records) records [] []
    (by simp [preparedSort]) (by simp [preparedSort,Encoding.sequence])
    (by simp [preparedSort]) (by simp [preparedSort]) (by simp [preparedSort])
    (by intro r allowed;fin_cases r <;> simp_all [preparedSort])
    (sortInput records).length (by simpa [preparedSort] using sourceLength)
  obtain ⟨finishTime,finishBound,finishing⟩:=finishSort_executes records
  refine ⟨_,?_,preparing.sequence (body.sequence finishing)⟩
  have countBound:records.length≤(sortInput records).length:=(records_length_le_sequence records).trans sourceLength
  let K:=(sortInput records).length+1
  have positive:1≤K:=by dsimp [K];omega
  have p2:K^2≤K^5:=Nat.pow_le_pow_right positive (by decide)
  have p3:K^3≤K^5:=Nat.pow_le_pow_right positive (by decide)
  have linear:K≤K^5:=Nat.le_self_pow (by decide) _
  have bodyTotal:bodyTime≤25000*K^5+2*K+1:=by
    have monotone:=Nat.mul_le_mul_right (25000*K^4+2) (show records.length≤K by dsimp [K];omega)
    have algebra:K*(25000*K^4+2)=25000*K^5+2*K:=by ring
    change bodyTime≤records.length*(25000*K^4+2)+1 at bodyBound
    rw [algebra] at monotone
    omega
  change prepareTime+1+(bodyTime+1+finishTime)≤30000*K^5
  change prepareTime≤1900*K^3 at prepareBound
  change finishTime≤100*K^2 at finishBound
  omega

/-- Exact stable ordering of the remapped signatures, retaining the
original indices used by the canonicalizer's mapping array. -/
theorem completeSort_indexed (vista : Executable.Vista) (mapping : Array Nat) (indices : List Nat) :
    sortOutput (indexedSignatures vista mapping indices).reverse=
      (Encoding.list recordCodec).encode (indexedSignatures vista mapping
        (indices.mergeSort (fun i j=>Executable.lexLE
          (Executable.referenceMap mapping (vista.node i)).key
          (Executable.referenceMap mapping (vista.node j)).key))) := by
  unfold sortOutput insertFold
  rw [indexedSignatures_sorted_fold]

end Counting.StackMachine.DagUpdate.Sort
