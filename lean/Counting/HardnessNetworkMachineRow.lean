import Counting.ExternalCoverNormalizeEmit
import Counting.StackLookupDrop
import Counting.StackRepeatBit

namespace Counting.HardnessNetworkMachine
open StackMachine StackMachine.Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

abbrev RowWorkspace (extra : Nat) := Fin 9 ↪ Fin (extra+9)
def rowHeaderPositions : Fin 6 ↪ Fin 9 := ⟨![0,2,6,8,7,4],by decide⟩
def RowWorkspace.header (w : RowWorkspace extra) : External.CoverNormalization.EmitWorkspace (extra+3) := rowHeaderPositions.trans w
def rowScratch : List (Fin 9) := [3,4,5,6,7,8]

def oneHotRow (width target : Nat) : List Nat :=
  List.replicate target 0++1::List.replicate (width-target-1) 0

theorem oneHotRow_length (width target : Nat) (inside : target<width) :
    (oneHotRow width target).length=width := by simp [oneHotRow];omega

theorem zero_sequence (count : Nat) :
    Encoding.sequence Encoding.natural (List.replicate count 0)=List.replicate count false := by
  induction count with
  | zero=>rfl
  | succ count ih=>
    simp only [List.replicate_succ,Encoding.sequence,ih]
    rfl

theorem sequence_append {α : Type} (codec : Encoding.Codec α) (a b : List α) :
    Encoding.sequence codec (a++b)=Encoding.sequence codec a++Encoding.sequence codec b := by
  induction a with
  | nil=>rfl
  | cons x xs ih=>simp only [List.cons_append,Encoding.sequence,ih,List.append_assoc]

theorem oneHotRow_encoding (width target : Nat) (inside : target<width) :
    (Encoding.list Encoding.natural).encode (oneHotRow width target)=
      Encoding.natural.encode width++List.replicate target false++Encoding.natural.encode 1++
        List.replicate (width-target-1) false := by
  change Encoding.natural.encode (oneHotRow width target).length++Encoding.sequence Encoding.natural (oneHotRow width target)=_
  rw [oneHotRow_length width target inside]
  simp only [oneHotRow,sequence_append,Encoding.sequence,zero_sequence,List.append_assoc]

/-- Emit a matrix row whose unique unit entry is at the supplied unary
index. Width and index counters are preserved; the output is accumulated
in reverse for the surrounding streaming serializer. -/
def emitOneHotRow (extra : Nat) (w : RowWorkspace extra) : Routine (extra+7) :=
  sequence (External.CoverNormalization.emitReversedNatural (extra+3) w.header)
    (sequence (ofProgram (ListPrograms.copyProgram (extra+6) (w 1) (w 3) (w 4)))
      (sequence (repeatBit (w 3) (w 2) false)
        (sequence (prepend (w 2) (Encoding.natural.encode 1).reverse)
          (sequence (ofProgram (ListPrograms.copyProgram (extra+6) (w 0) (w 5) (w 4)))
            (sequence (ofProgram (ListPrograms.copyProgram (extra+6) (w 1) (w 3) (w 4)))
              (sequence (ofProgram (Lookup.dropProgram (extra+7) (w 5) (w 3)))
                (sequence (discardBit (w 5)) (repeatBit (w 5) (w 2) false))))))))

theorem emitOneHotRow_executes (extra : Nat) (w : RowWorkspace extra)
    (store : Fin (extra+9) → List Bool) (inside : (store (w 1)).length<(store (w 0)).length)
    (empty : ∀ i∈rowScratch,store (w i)=[]) :
    ∃ time ≤ 100*((store (w 0)).length+(store (w 1)).length+1)^2,
      Executes (emitOneHotRow extra w) store time
        (Function.update store (w 2)
          (((Encoding.list Encoding.natural).encode
            (oneHotRow (store (w 0)).length (store (w 1)).length)).reverse++store (w 2))) := by
  let width:=(store (w 0)).length
  let target:=(store (w 1)).length
  obtain ⟨headerTime,headerBound,headerRun⟩:=External.CoverNormalization.emitReversedNatural_executes (extra+3) w.header store
    (by intro i member;fin_cases i <;> simp at member ⊢
        all_goals simp [RowWorkspace.header,rowHeaderPositions,empty,rowScratch])
  let header:=Function.update store (w 2) ((Encoding.natural.encode width).reverse++store (w 2))
  have headerAs : Executes (External.CoverNormalization.emitReversedNatural (extra+3) w.header) store headerTime header := by
    simpa [RowWorkspace.header,rowHeaderPositions,header,width] using headerRun
  have copyingIndex:=copy_executes (extra+6) (w 1) (w 3) (w 4)
    (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) header
    (by simp [header,w.injective.eq_iff,empty,rowScratch])
  have indexAt : header (w 1)=store (w 1) := by simp [header,w.injective.eq_iff]
  have counterEmpty : header (w 3)=[] := by simp [header,w.injective.eq_iff,empty,rowScratch]
  rw [indexAt,counterEmpty,List.append_nil] at copyingIndex
  let indexed:=Function.update header (w 3) (store (w 1))
  have prefixRun:=repeatBit_executes (w 3) (w 2) false (by simp [w.injective.eq_iff]) indexed
  let prefixed:=Function.update header (w 2) (List.replicate target false++header (w 2))
  have prefixFinal : Function.update (Function.update indexed (w 3) []) (w 2)
      (List.replicate (indexed (w 3)).length false++indexed (w 2))=prefixed := by
    funext r
    by_cases e3 : r=w 3
    · subst r;simp [prefixed,header,w.injective.eq_iff,empty,rowScratch]
    · simp [prefixed,indexed,Function.update_apply,e3,w.injective.eq_iff,target]
  have indexSize : (indexed (w 3)).length=target := by simp [indexed,target]
  rw [prefixFinal,indexSize] at prefixRun
  have unitRun:=prepend_executes (w 2) (Encoding.natural.encode 1).reverse prefixed
  let unitStore:=Function.update prefixed (w 2) ((Encoding.natural.encode 1).reverse++prefixed (w 2))
  have copyingWidth:=copy_executes (extra+6) (w 0) (w 5) (w 4)
    (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) unitStore
    (by simp [unitStore,prefixed,header,w.injective.eq_iff,empty,rowScratch])
  have widthAt : unitStore (w 0)=store (w 0) := by simp [unitStore,prefixed,header,w.injective.eq_iff]
  have remainderEmpty : unitStore (w 5)=[] := by simp [unitStore,prefixed,header,w.injective.eq_iff,empty,rowScratch]
  rw [widthAt,remainderEmpty,List.append_nil] at copyingWidth
  let widened:=Function.update unitStore (w 5) (store (w 0))
  have copyingDrop:=copy_executes (extra+6) (w 1) (w 3) (w 4)
    (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) widened
    (by simp [widened,unitStore,prefixed,header,w.injective.eq_iff,empty,rowScratch])
  have indexAgain : widened (w 1)=store (w 1) := by simp [widened,unitStore,prefixed,header,w.injective.eq_iff]
  have counterAgain : widened (w 3)=[] := by simp [widened,unitStore,prefixed,header,w.injective.eq_iff,empty,rowScratch]
  rw [indexAgain,counterAgain,List.append_nil] at copyingDrop
  let dropReady:=Function.update widened (w 3) (store (w 1))
  have dropping:=Lookup.drop_executes (extra+7) (w 5) (w 3) (by simp [w.injective.eq_iff]) dropReady
  let dropped:=Function.update unitStore (w 5) ((store (w 0)).drop target)
  have dropFinal : Function.update (Function.update dropReady (w 3) []) (w 5)
      ((dropReady (w 5)).drop (dropReady (w 3)).length)=dropped := by
    funext r
    by_cases e3 : r=w 3
    · subst r;simp [dropped,unitStore,prefixed,header,w.injective.eq_iff,empty,rowScratch]
    · by_cases e5 : r=w 5
      · subst r;simp [dropped,dropReady,widened,w.injective.eq_iff,target]
      · simp [dropped,dropReady,widened,e3,e5]
  have dropIndex : (dropReady (w 3)).length=target := by simp [dropReady,target]
  rw [dropFinal,dropIndex] at dropping
  have skipping:=discardBit_executes (w 5) dropped
  let remaining:=Function.update unitStore (w 5) (((store (w 0)).drop target).tail)
  have skipAs : Executes (discardBit (w 5)) dropped 1 remaining := by simpa [remaining,dropped] using skipping
  have suffixRun:=repeatBit_executes (w 5) (w 2) false (by simp [w.injective.eq_iff]) remaining
  have remainingSize : (remaining (w 5)).length=width-target-1 := by simp [remaining,width,Nat.sub_sub]
  have final : Function.update (Function.update remaining (w 5) []) (w 2)
      (List.replicate (remaining (w 5)).length false++remaining (w 2))=
      Function.update store (w 2)
      (((Encoding.list Encoding.natural).encode (oneHotRow width target)).reverse++store (w 2)) := by
    rw [remainingSize,oneHotRow_encoding width target inside]
    funext r
    by_cases e2 : r=w 2
    · subst r;simp [remaining,unitStore,prefixed,header,w.injective.eq_iff,List.reverse_append,List.append_assoc]
    · by_cases e5 : r=w 5
      · subst r;simp [w.injective.eq_iff,empty,rowScratch]
      · simp [remaining,unitStore,prefixed,header,e2,e5]
  rw [final,remainingSize] at suffixRun
  have composed:=headerAs.sequence (copyingIndex.sequence (prefixRun.sequence
    (unitRun.sequence (copyingWidth.sequence (copyingDrop.sequence
      (dropping.sequence (skipAs.sequence suffixRun)))))))
  have unitLength : (Encoding.natural.encode 1).reverse.length=3 := rfl
  rw [unitLength] at composed
  refine ⟨_,?_,composed⟩
  change headerTime ≤ 30*(width+1)^2 at headerBound
  change _ ≤ 100*(width+target+1)^2
  have shorter : width-target-1 ≤ width := by omega
  change headerTime+1+(5*target+2+1+(3*target+1+1+(2*3+1+(5*width+2+1+
    (5*target+2+1+(2*target+1+1+(1+1+(3*(width-target-1)+1)))))))) ≤ _
  nlinarith only [headerBound,shorter,Nat.zero_le width,Nat.zero_le target]

end Counting.HardnessNetworkMachine
