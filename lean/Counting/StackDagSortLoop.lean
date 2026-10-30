import Counting.StackDagSortStep
import Counting.DagSortInsertionSpec

namespace Counting.StackMachine.DagUpdate.Sort
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

def insertionLoop : Routine 94 := forEach 90 insertionStep

def insertionLoopResult (store : Store 94) (query : Record) (records : List Record)
    (suffix : List Bool) (inserted : Bool) : Store 94 :=
  let result := scanRecords query inserted records
  Function.update (Function.update (Function.update (Function.update store 90 []) 80 suffix)
    84 [result.2]) 83 ((Encoding.sequence recordCodec result.1).reverse++store 83)

/-- A charged loop scans each serialized indexed node once. The compact
output may grow, but no iteration scans that accumulated output for free. -/
theorem insertionLoop_executes (store : Store 94) (query : Record) (records : List Record)
    (suffix : List Bool) (inserted : Bool) (sourceLength : Nat)
    (source : store 80=Encoding.sequence recordCodec records++suffix)
    (queryAt : store 64=Encoding.node.encode query.2) (recordAt : store 82=recordCodec.encode query)
    (status : store 81=[true]) (flagAt : store 84=[inserted])
    (counter : store 90=List.replicate records.length true) (size : (store 80).length ≤ sourceLength)
    (empty : ∀ r : Fin 96,r.val≤14 ∨ (40≤r.val ∧ r.val≤44) ∨ (49≤r.val ∧ r.val≤51) ∨
      r=65 ∨ r=66 ∨ r=67 ∨ r=86 ∨ r=88 ∨ r=89 → store r=[]) :
    ∃ time≤records.length*(15000*(sourceLength+(store 82).length+1)^3+2)+1,
      Executes insertionLoop store time (insertionLoopResult store query records suffix inserted) := by
  induction records generalizing store inserted with
  | nil =>
    have emptyCounter : store 90=[] := by simpa using counter
    obtain ⟨ran,halted⟩ := repeat_empty (90:Fin 96) insertionStep store emptyCounter
    have final : store=insertionLoopResult store query [] suffix inserted := by
      have sourceAt : store 80=suffix := by simpa [Encoding.sequence] using source
      funext r
      by_cases r90 : r=90 <;> by_cases r80 : r=80 <;> by_cases r84 : r=84 <;> by_cases r83 : r=83 <;>
        simp [insertionLoopResult,scanRecords,Encoding.sequence,r90,r80,r84,r83,emptyCounter,sourceAt,flagAt]
    exact ⟨1,by simp,⟨1,store⟩,ran,halted,final⟩
  | cons current rest ih =>
    let tailStore := Function.update store 90 (List.replicate rest.length true)
    let remaining := Encoding.sequence recordCodec rest++suffix
    let before := Executable.lexLE query.2.key current.2.key
    obtain ⟨bodyTime,bodyBound,bodyExec⟩ := insertionStep_executes tailStore query current remaining inserted
      (by simpa [tailStore,remaining,Encoding.sequence,List.append_assoc] using source)
      (by simp [tailStore,queryAt]) (by simp [tailStore,recordAt])
      (by simp [tailStore,status]) (by simp [tailStore,flagAt]) (by
        intro r allowed
        have ne90 : r ≠ 90 := by intro equal; subst r; norm_num [Fin.ext_iff] at allowed
        simpa [tailStore,ne90] using empty r allowed)
    let middle := insertionStepResult tailStore query current remaining inserted
    have middleSource : middle 80=Encoding.sequence recordCodec rest++suffix := by
      simp [middle,insertionStepResult,remaining]
    have middleQuery : middle 64=Encoding.node.encode query.2 := by simp [middle,insertionStepResult,tailStore,queryAt]
    have middleRecord : middle 82=recordCodec.encode query := by simp [middle,insertionStepResult,tailStore,recordAt]
    have middleStatus : middle 81=[true] := by simp [middle,insertionStepResult,tailStore,status]
    have middleFlag : middle 84=[inserted || before] := by simp [middle,insertionStepResult,before]
    have middleCounter : middle 90=List.replicate rest.length true := by simp [middle,insertionStepResult,tailStore]
    have middleSize : (middle 80).length ≤ sourceLength := by
      rw [middleSource]
      rw [source] at size
      simp only [Encoding.sequence,List.length_append] at size ⊢
      omega
    have middleEmpty : ∀ r : Fin 96,r.val≤14 ∨ (40≤r.val ∧ r.val≤44) ∨ (49≤r.val ∧ r.val≤51) ∨
        r=65 ∨ r=66 ∨ r=67 ∨ r=86 ∨ r=88 ∨ r=89 → middle r=[] := by
      intro r allowed
      have ne80 : r ≠ 80 := by intro equal; subst r; norm_num [Fin.ext_iff] at allowed
      have ne83 : r ≠ 83 := by intro equal; subst r; norm_num [Fin.ext_iff] at allowed
      have ne84 : r ≠ 84 := by intro equal; subst r; norm_num [Fin.ext_iff] at allowed
      have ne90 : r ≠ 90 := by intro equal; subst r; norm_num [Fin.ext_iff] at allowed
      simpa [middle,insertionStepResult,tailStore,ne80,ne83,ne84,ne90] using empty r allowed
    obtain ⟨tailTime,tailBound,tailExec⟩ := ih middle (inserted || before) middleSource middleQuery middleRecord
      middleStatus middleFlag middleCounter middleSize middleEmpty
    obtain ⟨bodyFinal,bodyRun,bodyHalt,bodyStore⟩ := bodyExec
    obtain ⟨finish,tailRun,tailHalt,tailStoreResult⟩ := tailExec
    have first := repeat_iteration (90:Fin 96) insertionStep store true (List.replicate rest.length true)
      (by simpa [List.length_cons,List.replicate_succ] using counter) bodyTime bodyFinal bodyRun bodyHalt
    change Machine.run (step insertionLoop.program) (bodyTime+2) ⟨0,store⟩=some ⟨0,bodyFinal.store⟩ at first
    have final : insertionLoopResult middle query rest suffix (inserted || before)=
        insertionLoopResult store query (current::rest) suffix inserted := by
      funext r
      by_cases r90 : r=90 <;> by_cases r80 : r=80 <;> by_cases r84 : r=84 <;> by_cases r83 : r=83 <;>
        cases inserted <;> cases comparison : Executable.lexLE query.2.key current.2.key <;>
        simp [insertionLoopResult,scanRecords,middle,insertionStepResult,tailStore,before,
          recordLE,←recordAt,remaining,Encoding.sequence,List.reverse_append,List.append_assoc,
          r90,r80,r84,r83,comparison]
    refine ⟨bodyTime+2+tailTime,?_,finish,?_,tailHalt,tailStoreResult.trans final⟩
    · have bodyLimit : bodyTime≤15000*(sourceLength+(store 82).length+1)^3 := by
        have enlarge : ((tailStore 80).length+(tailStore 82).length+1)^3≤
            (sourceLength+(store 82).length+1)^3 := by simp only [tailStore,Function.update_of_ne (by decide : (80:Fin 96)≠90),Function.update_of_ne (by decide : (82:Fin 96)≠90)];gcongr
        exact bodyBound.trans (Nat.mul_le_mul_left 15000 enlarge)
      have fixed : middle 82=store 82 := by simp [middle,insertionStepResult,tailStore]
      rw [fixed] at tailBound
      simp only [List.length_cons]
      nlinarith
    · rw [Machine.run_add,first,Option.bind_some,bodyStore]
      exact tailRun

end Counting.StackMachine.DagUpdate.Sort
