import Counting.StackEncodingBoundedNatural
import Counting.StackRealizabilityWeightLookup

namespace Counting.StackMachine.DagUpdate
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

abbrev ReferenceWorkspace (extra : Nat) := Fin 14 ↪ Fin (extra+14)

def ReferenceWorkspace.counter (w : ReferenceWorkspace extra) : CountWorkspace (extra+3) :=
  (⟨![1,3,5,6,7,8,4,9,10,11,12],by decide⟩ : Fin 11 ↪ Fin 14).trans w

def ReferenceWorkspace.reader (w : ReferenceWorkspace extra) : Fin 8 ↪ Fin (extra+14) :=
  (⟨![0,3,2,4,5,6,7,8],by decide⟩ : Fin 8 ↪ Fin 14).trans w

/-- Binary array access clips the unary scan to the actual input bit length.
Out-of-range references return zero, exactly as `Array.getD`. -/
def referenceLookup (extra : Nat) (w : ReferenceWorkspace extra) : Routine (extra+12) :=
  sequence (ofProgram (ListPrograms.copyProgram (extra+11) (w 0) (w 12) (w 13)))
    (sequence (boundedCount (extra+3) w.counter)
      (sequence (RealizabilityCheck.weightLookup (extra+6) w.reader)
        (sequence (clear (w 3)) (discardBit (w 4)))))

theorem clipped_reference (values : List Nat) (index budget : Nat) (long : values.length ≤ budget) :
    values[min index budget]?.getD 0=values[index]?.getD 0 := by
  by_cases fits : index ≤ budget
  · rw [Nat.min_eq_left fits]
  · have outside : values.length ≤ index := by omega
    rw [Nat.min_eq_right (by omega)]
    simp [List.getElem?_eq_none (by omega : values.length ≤ budget),List.getElem?_eq_none outside]

theorem referenceLookup_executes (extra : Nat) (w : ReferenceWorkspace extra) (store : Store (extra+12))
    (values : List Nat) (index : Nat)
    (source : store (w 0)=(Encoding.list Encoding.natural).encode values)
    (query : store (w 1)=Encoding.natural.encode index)
    (empty : ∀ j : Fin 14,j≠0 → j≠1 → j≠2 → store (w j)=[]) :
    ∃ time ≤ 200*((store (w 0)).length+(store (w 1)).length+1)^3,
      Executes (referenceLookup extra w) store time
        (Function.update store (w 2) ((values[index]?.getD 0).bits++store (w 2))) := by
  have copying:=copy_executes (extra+11) (w 0) (w 12) (w 13)
    (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff])
    store (empty 13 (by decide) (by decide) (by decide))
  rw [empty 12 (by decide) (by decide) (by decide),List.append_nil] at copying
  let copied:=Function.update store (w 12) (store (w 0))
  obtain ⟨countTime,countBound,countRun⟩:=boundedNatural_executes (extra+3) w.counter copied index
    (by simp [ReferenceWorkspace.counter,copied,w.injective.eq_iff,query])
    (by simp [ReferenceWorkspace.counter,copied,w.injective.eq_iff,empty]) (by
      intro i member
      fin_cases i <;> simp_all [ReferenceWorkspace.counter,copied,w.injective.eq_iff])
  let clipped:=min index (store (w 0)).length
  let counted:=boundedNaturalResult (extra+3) w.counter copied index
  have unary : counted (w 3)=List.replicate clipped true := by
    simp [counted,boundedNaturalResult,ReferenceWorkspace.counter,copied,w.injective.eq_iff,clipped]
  have flag : counted (w 4)=[decide (index ≤ (store (w 0)).length)] := by
    simp [counted,boundedNaturalResult,ReferenceWorkspace.counter,copied,w.injective.eq_iff,empty]
  obtain ⟨readTime,readBound,readRun⟩:=RealizabilityCheck.weightLookup_executes (extra+6) w.reader counted values
    (by simp [ReferenceWorkspace.reader,counted,boundedNaturalResult,ReferenceWorkspace.counter,
      copied,w.injective.eq_iff,source])
    (by simp [ReferenceWorkspace.reader,counted,boundedNaturalResult,ReferenceWorkspace.counter,copied,w.injective.eq_iff,empty])
    (by simp [ReferenceWorkspace.reader,counted,boundedNaturalResult,ReferenceWorkspace.counter,copied,w.injective.eq_iff,empty])
    (by simp [ReferenceWorkspace.reader,counted,boundedNaturalResult,ReferenceWorkspace.counter,copied,w.injective.eq_iff,empty])
    (by simp [ReferenceWorkspace.reader,counted,boundedNaturalResult,ReferenceWorkspace.counter,copied,w.injective.eq_iff,empty])
  have inputLength : values.length ≤ (store (w 0)).length := by
    rw [source]
    have seqBound (xs : List Nat) : xs.length ≤ (Encoding.sequence Encoding.natural xs).length := by
      induction xs with
      | nil=>simp [Encoding.sequence]
      | cons head rest ih=>
        simp only [Encoding.sequence,List.length_append,List.length_cons,Encoding.natural_length]
        omega
    have bounded:=seqBound values
    simp only [Encoding.list,List.length_append]
    omega
  have same:=clipped_reference values index (store (w 0)).length inputLength
  have readerIndex : counted (w.reader 1)=List.replicate clipped true := unary
  rw [readerIndex,List.length_replicate] at readRun readBound
  change Executes _ counted readTime
    (Function.update counted (w 2) ((values[clipped]?.getD 0).bits++counted (w 2))) at readRun
  rw [same] at readRun
  have outputSame : counted (w 2)=store (w 2) := by
    simp [counted,boundedNaturalResult,ReferenceWorkspace.counter,copied,w.injective.eq_iff]
  rw [outputSame] at readRun
  let read:=Function.update counted (w 2) ((values[index]?.getD 0).bits++store (w 2))
  have clearing:=clear_executes (w 3) read
  have counterAt : read (w 3)=List.replicate clipped true := by simp [read,w.injective.eq_iff,unary]
  rw [counterAt,List.length_replicate] at clearing
  let cleaned:=Function.update read (w 3) []
  have discarding:=discardBit_executes (w 4) cleaned
  have flagAt : cleaned (w 4)=[decide (index ≤ (store (w 0)).length)] := by
    simp [cleaned,read,w.injective.eq_iff,flag]
  rw [flagAt,List.tail_cons] at discarding
  have final : Function.update cleaned (w 4) []=
      Function.update store (w 2) ((values[index]?.getD 0).bits++store (w 2)) := by
    funext r
    by_cases r3 : r=w 3
    · subst r;simp [cleaned,w.injective.eq_iff,empty]
    · by_cases r4 : r=w 4
      · subst r;simp [w.injective.eq_iff,empty]
      · by_cases r12 : r=w 12
        · subst r;simp [cleaned,read,counted,boundedNaturalResult,ReferenceWorkspace.counter,w.injective.eq_iff,empty]
        · by_cases r2 : r=w 2 <;>
            simp [cleaned,read,counted,boundedNaturalResult,ReferenceWorkspace.counter,copied,
              r2,r3,r4,r12]
  rw [final] at discarding
  have inputAt : counted (w.reader 0)=store (w 0) := by
    simp [ReferenceWorkspace.reader,counted,boundedNaturalResult,ReferenceWorkspace.counter,copied,w.injective.eq_iff]
  have budgetAt : copied (w.counter 10)=store (w 0) := by simp [ReferenceWorkspace.counter,copied]
  rw [inputAt] at readBound
  rw [budgetAt,←query] at countBound
  have bounded : clipped ≤ (store (w 0)).length := Nat.min_le_right _ _
  let K:=(store (w 0)).length+(store (w 1)).length+1
  have positive : 1 ≤ K := by omega
  have sourceBound : (store (w 0)).length ≤ K := by omega
  have square : K ≤ K^2 := by nlinarith only [positive]
  have cube : K ≤ K^3 := by nlinarith only [positive,square]
  refine ⟨_,?_,copying.sequence (countRun.sequence (readRun.sequence (clearing.sequence discarding)))⟩
  change _ ≤ 200*K^3
  change countTime ≤ 64*K^3 at countBound
  nlinarith only [countBound,readBound,bounded,positive,sourceBound,cube]

end Counting.StackMachine.DagUpdate
