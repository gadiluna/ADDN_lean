import Counting.StackDagCanonicalLevelCalls
import Counting.StackDagIncrement

namespace Counting.StackMachine.DagUpdate.Canonical
open Routine RealizabilityCall Executable
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

def oneLevel : Routine 128 :=
  sequence (copyExternal 20 27)
    (sequence (pushBit (context 28) true)
      (sequence levelCollect (sequence levelSort
        (sequence levelCommit (sequence (clearExternal 28)
          (DagValidation.incrementRoutine 127 0 (context 22) 1))))))

def oneLevelData (data : Fin 30 → List Bool) (next : CanonicalState) (level : Nat) : Fin 30 → List Bool :=
  Function.update (Function.update (Function.update data
    1 ((Encoding.array Encoding.natural).encode next.2))
    2 ((Encoding.array Encoding.node).encode next.1)) 22 (level+1).bits

def oneLevelCoefficient : Nat :=
  collectCoefficient*4^8+30000*101^5+commitRecordsCoefficient*103^9+10000

private theorem cap_power (a K exponent : Nat) {base : Nat} (bound : base ≤ a*K^3) :
    base^exponent ≤ a^exponent*K^(3*exponent) := by
  have h := Nat.pow_le_pow_left bound exponent
  simpa only [Nat.mul_pow,←Nat.pow_mul] using h

private theorem level_arithmetic (collectCoeff commitCoeff B source tc ts tm ti : Nat)
    (sourceBound : source ≤ B)
    (collectBound : tc ≤ collectCoeff*4^8*(B+1)^8)
    (sortBound : ts ≤ 30000*101^5*(B+1)^15)
    (commitBound : tm ≤ commitCoeff*103^9*(B+1)^27)
    (incrementBound : ti ≤ 4*B+7) :
    5*source+2+1+(1+1+(tc+1+(ts+1+(tm+1+(2+1+ti))))) ≤
      (collectCoeff*4^8+30000*101^5+commitCoeff*103^9+10000)*(B+1)^27 := by
  have positive : 1 ≤ B+1 := by omega
  have p8 : (B+1)^8 ≤ (B+1)^27 := Nat.pow_le_pow_right positive (by decide)
  have p15 : (B+1)^15 ≤ (B+1)^27 := Nat.pow_le_pow_right positive (by decide)
  have linear : B+1 ≤ (B+1)^27 := Nat.le_self_pow (by decide) _
  have one : 1 ≤ (B+1)^27 := Nat.one_le_pow' _ _
  have c := collectBound.trans (Nat.mul_le_mul_left (collectCoeff*4^8) p8)
  have s := sortBound.trans (Nat.mul_le_mul_left (30000*101^5) p15)
  simp only [Nat.add_mul]
  omega

/-- A whole canonical level physically collects remapped signatures, sorts
them stably, interns them, and increments the binary level. Its caller's
persistent fields survive unchanged except for the map, pool and level. -/
theorem oneLevel_executes (data : Fin 30 → List Bool) (source : Vista)
    (valid : NodesValid source) (state : CanonicalState) (level : Nat)
    (sameSize : state.2.size=source.nodes.size)
    (sourceAt : data 20=(Encoding.array Encoding.node).encode source.nodes)
    (mapAt : data 1=(Encoding.array Encoding.natural).encode state.2)
    (poolAt : data 2=(Encoding.array Encoding.node).encode state.1)
    (levelAt : data 22=level.bits)
    (e26 : data 26=[]) (e27 : data 27=[]) (e28 : data 28=[]) (e29 : data 29=[])
    (B : Nat) (bounded : ∀r,(data r).length ≤ B) :
    ∃ time ≤ oneLevelCoefficient*(B+1)^27,
      Executes oneLevel (file data) time (file (oneLevelData data (canonicalLevel source state level) level)) := by
  let records := (collectEntries state.2 level 0 source.nodes.toList).reverse
  let sorted := Sort.insertFold records []
  have sortedEq : sorted=(Sort.indexedSignatures source state.2 (levelNodes source level)).insertionSort
      (fun a b=>Sort.recordLE a b=true) := by
    dsimp only [sorted,records,Sort.insertFold]
    rw [collectEntries_source,List.foldl_reverse]
    rfl
  have inside : ∀ record∈sorted,record.1 < state.2.size := by
    intro record member
    rw [sortedEq,List.mem_insertionSort] at member
    rw [←collectEntries_source] at member
    rw [sameSize]
    exact collectEntries_index_lt source state.2 level record member
  have stateEq : sorted.foldl commitRecord state=canonicalLevel source state level := by
    rw [sortedEq,canonicalLevel_records source valid]
  have copied := copyExternal_executes data 20 27 (by decide)
  rw [e27,List.append_nil] at copied
  let a := Function.update data 27 (data 20)
  have flagged := pushBit_executes (context 28) true (file a)
  rw [file_context,show a 28=[] by simp [a,e28],file_update] at flagged
  let b := Function.update a 28 [true]
  obtain ⟨tc,bc,rc⟩ := levelCollect_executes b source state.2 level
    (by simp [b,a,sourceAt]) (by simp [b,a,mapAt]) (by simp [b,a,levelAt])
    (by simp [b]) (by simp [b,a,e26])
  let c := Function.update (Function.update b 27 []) 26 ((Encoding.list Sort.recordCodec).encode records)
  obtain ⟨ts,bs,rs⟩ := levelSort_executes c records
    (by simp [c,Sort.sortInput]) (by simp [c,b,a,e29])
  let d := Function.update (Function.update c 26 []) 29 (Sort.sortOutput records)
  obtain ⟨tm,bm,rm⟩ := levelCommit_executes d state sorted inside
    (by simp [d,Sort.sortOutput,sorted]) (by simp [d,c,b,a,mapAt])
    (by simp [d,c,b,a,poolAt]) (by simp [d,c,b])
  let e := levelCommittedData d (sorted.foldl commitRecord state)
  have cleared := clearExternal_executes e 28
  rw [show e 28=[true] by simp [e,levelCommittedData,d,c,b],List.length_singleton] at cleared
  let f := Function.update e 28 []
  obtain ⟨ti,bi,ri⟩ := DagValidation.increment_natural 127 0 (context 22) 1
    (by decide) (by decide) (by decide) (file f) (by simp [file]) (by simp [file]) level
    (by simp [f,e,levelCommittedData,d,c,b,a,levelAt])
  rw [file_update] at ri
  have final : Function.update f 22 (level+1).bits=oneLevelData data (canonicalLevel source state level) level := by
    funext r
    fin_cases r <;> simp [oneLevelData,f,e,levelCommittedData,d,c,b,a,e26,e27,e28,e29,stateEq]
  rw [final] at ri
  have sourceBound : ((Encoding.array Encoding.node).encode source.nodes).length ≤ B := by
    rw [←sourceAt];exact bounded 20
  have mapBound : ((Encoding.array Encoding.natural).encode state.2).length ≤ B := by
    rw [←mapAt];exact bounded 1
  have poolBound : ((Encoding.array Encoding.node).encode state.1).length ≤ B := by
    rw [←poolAt];exact bounded 2
  have levelBound : level.size ≤ B := by
    have h := bounded 22
    rw [levelAt,Encoding.bits_length] at h
    exact h
  have nodesBound : source.nodes.size ≤ B :=
    (Encoding.array_size_le_length Encoding.node source.nodes
      (fun node _=>Encoding.node_positive_length node)).trans sourceBound
  have recordsBound : ((Encoding.list Sort.recordCodec).encode records).length ≤ 100*(B+1)^3 := by
    apply collectEntries_encoded_cap state.2 level 0 source.nodes.toList (B+1) (by omega)
    · simpa only [Encoding.array,Encoding.transport] using sourceBound.trans (Nat.le_succ B)
    · exact mapBound.trans (Nat.le_succ B)
    · simp only [Nat.zero_add,Array.length_toList];omega
  have sortedLength : (Sort.sortOutput records).length=((Encoding.list Sort.recordCodec).encode records).length := by
    simp [Sort.sortOutput,Encoding.list,Sort.insertFold_length,List.length_append,
      Sort.insertFold_encoded_length,Encoding.sequence]
  have collectBase : (b 27).length+(b 1).length+(b 22).length+1 ≤ 4*(B+1) := by
    have b20 := bounded 20
    have b1 := bounded 1
    have b22 := bounded 22
    simp only [b,a,Function.update_of_ne (show (27:Fin 30)≠28 by decide),Function.update_self,
      Function.update_of_ne (show (1:Fin 30)≠28 by decide),Function.update_of_ne (show (1:Fin 30)≠27 by decide),
      Function.update_of_ne (show (22:Fin 30)≠28 by decide),Function.update_of_ne (show (22:Fin 30)≠27 by decide)]
    omega
  have collectCost : tc ≤ collectCoefficient*4^8*(B+1)^8 := by
    have h := bc.trans (Nat.mul_le_mul_left collectCoefficient (Nat.pow_le_pow_left collectBase 8))
    simpa only [Nat.mul_pow,Nat.mul_assoc] using h
  have positive : 1 ≤ B+1 := by omega
  have linear : B+1 ≤ (B+1)^3 := Nat.le_self_pow (by decide) _
  have sortBase : (c 26).length+1 ≤ 101*(B+1)^3 := by
    simp only [c,Function.update_self];omega
  have sortCost : ts ≤ 30000*101^5*(B+1)^15 := by
    have h := bs.trans (Nat.mul_le_mul_left 30000 (cap_power 101 (B+1) 5 sortBase))
    simpa only [Nat.mul_assoc] using h
  have commitBase : (d 2).length+(d 1).length+(d 29).length+1 ≤ 103*(B+1)^3 := by
    have b2 := bounded 2
    have b1 := bounded 1
    simp only [d,c,b,a,Function.update_self,Function.update_of_ne (show (2:Fin 30)≠29 by decide),
      Function.update_of_ne (show (2:Fin 30)≠26 by decide),Function.update_of_ne (show (2:Fin 30)≠27 by decide),
      Function.update_of_ne (show (2:Fin 30)≠28 by decide),Function.update_of_ne (show (1:Fin 30)≠29 by decide),
      Function.update_of_ne (show (1:Fin 30)≠26 by decide),Function.update_of_ne (show (1:Fin 30)≠27 by decide),
      Function.update_of_ne (show (1:Fin 30)≠28 by decide),sortedLength]
    omega
  have commitCost : tm ≤ commitRecordsCoefficient*103^9*(B+1)^27 := by
    have h := bm.trans (Nat.mul_le_mul_left commitRecordsCoefficient (cap_power 103 (B+1) 9 commitBase))
    simpa only [Nat.mul_assoc] using h
  refine ⟨_,?_,copied.sequence (flagged.sequence (rc.sequence (rs.sequence (rm.sequence (cleared.sequence ri)))))⟩
  exact level_arithmetic collectCoefficient commitRecordsCoefficient B (data 20).length tc ts tm ti
    (bounded 20) collectCost sortCost commitCost (by omega)

end Counting.StackMachine.DagUpdate.Canonical

