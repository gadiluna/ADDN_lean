import Counting.StackEncodingBoundedNatural
import Counting.StackLookupPreserving
import Counting.StackEncodingListItem

namespace Counting.External.SATVerification
open StackMachine StackMachine.Routine StackMachine.EncodingPrograms
set_option backward.isDefEq.respectTransparency false

/-- Header, assignment, unary index, consumed budget, value, flag, then
seven temporary registers. Indices are never expanded beyond the assignment. -/
abbrev LookupWorkspace (extra : Nat) := Fin 13 ↪ Fin (extra+13)

def lookupCountRoles (extra : Nat) (w : LookupWorkspace extra) : CountWorkspace (extra+2) :=
  ⟨fun i => w (![0,2,6,7,8,9,5,10,11,12,3] i),by
    intro i j same
    have equal := w.injective same
    fin_cases i <;> fin_cases j <;> simp_all⟩

def lookupBitRoles (extra : Nat) (w : LookupWorkspace extra) : Fin 7 ↪ Fin (extra+13) :=
  ⟨fun i => w (![1,2,4,5,6,7,8] i),by
    intro i j same
    have equal := w.injective same
    fin_cases i <;> fin_cases j <;> simp_all⟩

def boundedLookup (extra : Nat) (w : LookupWorkspace extra) : Routine (extra+11) :=
  sequence (ofProgram (ListPrograms.copyProgram (extra+10) (w 1) (w 3) (w 6)))
    (sequence (boundedCount (extra+2) (lookupCountRoles extra w))
      (sequence (Lookup.preservingLookup (extra+6) (lookupBitRoles extra w))
        (sequence (ofProgram (combineFlagsProgram (extra+11) (w 5))) (clear (w 2)))))

theorem boundedLookup_executes (extra : Nat) (w : LookupWorkspace extra)
    (store : Fin (extra+13) → List Bool) (index : Nat)
    (header : store (w 0)=Encoding.natural.encode index)
    (empty : ∀ i : Fin 13,i∈([2,3,6,7,8,9,10,11,12] : List (Fin 13)) → store (w i)=[]) :
    ∃ time ≤ 100*((store (w 1)).length+(store (w 0)).length+1)^3,
      Executes (boundedLookup extra w) store time
        (Function.update (Function.update store (w 4) ((store (w 1))[index]?.toList++store (w 4)))
          (w 5) ((store (w 1))[index]?.isSome::store (w 5))) := by
  have ne (i j : Fin 13) (h : i≠j) : w i≠w j := fun same => h (w.injective same)
  let bits := store (w 1)
  let bounded := min index bits.length
  let copied := Function.update store (w 3) bits
  have copying : Executes (ofProgram (ListPrograms.copyProgram (extra+10) (w 1) (w 3) (w 6)))
      store (5*bits.length+2) copied := by
    simpa +instances only [ListPrograms.copyProgram,bits,copied,empty 3 (by decide),List.append_nil] using
      copy_executes (extra+10) (w 1) (w 3) (w 6) (ne 1 3 (by decide)) (ne 1 6 (by decide))
        (ne 3 6 (by decide)) store (empty 6 (by decide))
  have countHeader : copied ((lookupCountRoles extra w) 0)=Encoding.natural.encode index := by
    simpa [copied,lookupCountRoles,w.injective.eq_iff] using header
  have countEmpty : copied ((lookupCountRoles extra w) 1)=[] := by
    simp [copied,lookupCountRoles,w.injective.eq_iff,empty 2 (by decide)]
  have workEmpty (i : Fin 11) (member : i∈({2,3,4,5,7,8,9}:Finset (Fin 11))) :
      copied ((lookupCountRoles extra w) i)=[] := by
    fin_cases i <;> simp only [Finset.mem_insert,Finset.mem_singleton] at member
    all_goals first | contradiction | simp [copied,lookupCountRoles,w.injective.eq_iff,empty]
  obtain ⟨countTime,countBound,countRun⟩ := boundedNatural_executes (extra+2) (lookupCountRoles extra w)
    copied index countHeader countEmpty workEmpty
  let counted := Function.update (Function.update store (w 2) (List.replicate bounded true))
    (w 5) (decide (index≤bits.length)::store (w 5))
  have countedEq : boundedNaturalResult (extra+2) (lookupCountRoles extra w) copied index=counted := by
    funext r
    by_cases a : r=w 3
    · subst r; simp [boundedNaturalResult,lookupCountRoles,copied,counted,w.injective.eq_iff,empty 3 (by decide)]
    · simp [boundedNaturalResult,lookupCountRoles,copied,counted,Function.update_apply,a,bounded,bits,w.injective.eq_iff]
  rw [countedEq] at countRun
  let found := bits[bounded]?
  let read := Function.update (Function.update counted (w 4) (found.toList++store (w 4)))
    (w 5) (found.isSome::decide (index≤bits.length)::store (w 5))
  have reading : Executes (Lookup.preservingLookup (extra+6) (lookupBitRoles extra w)) counted
      (Lookup.lookupCost bits (List.replicate bounded true)) read := by
    simpa [lookupBitRoles,counted,read,found,bits,w.injective.eq_iff] using
      Lookup.preservingLookup_executes (extra+6) (lookupBitRoles extra w) counted
        (by simp [lookupBitRoles,counted,w.injective.eq_iff,empty 6 (by decide)])
        (by simp [lookupBitRoles,counted,w.injective.eq_iff,empty 7 (by decide)])
        (by simp [lookupBitRoles,counted,w.injective.eq_iff,empty 8 (by decide)])
  have readFlag : read (w 5)=found.isSome::decide (index≤bits.length)::store (w 5) := by simp [read]
  have combine := combineFlags_executes (extra+11) (w 5) read (decide (index≤bits.length)) found.isSome
    (store (w 5)) readFlag
  let combined := Function.update read (w 5) ((decide (index≤bits.length) && found.isSome)::store (w 5))
  have clearing := clear_executes (w 2) combined
  have currentIndex : combined (w 2)=List.replicate bounded true := by
    simp [combined,read,counted,w.injective.eq_iff]
  rw [currentIndex,List.length_replicate] at clearing
  have foundEq : found=bits[index]? := by
    by_cases fits : index≤bits.length
    · simp [found,bounded,Nat.min_eq_left fits]
    · have large : bits.length≤ index := by omega
      simp [found,bounded,Nat.min_eq_right large,List.getElem?_eq_none (by omega : bits.length≤ index)]
  have flagEq : (decide (index≤bits.length) && found.isSome)=bits[index]?.isSome := by
    rw [foundEq]
    by_cases fits : index≤bits.length
    · simp [fits]
    · simp [fits,List.getElem?_eq_none (by omega : bits.length≤ index)]
  have restored : Function.update combined (w 2) []=
      Function.update (Function.update store (w 4) (bits[index]?.toList++store (w 4)))
        (w 5) (bits[index]?.isSome::store (w 5)) := by
    funext r
    by_cases a : r=w 2
    · subst r; simp [w.injective.eq_iff,empty 2 (by decide)]
    · by_cases b : r=w 5
      · subst r; simp only [Function.update_of_ne a,combined,Function.update_self,flagEq]
      · simp [combined,read,counted,Function.update_apply,a,b,foundEq]
  rw [restored] at clearing
  have result := copying.sequence (countRun.sequence (reading.sequence (combine.sequence clearing)))
  refine ⟨5*bits.length+2+1+(countTime+1+(Lookup.lookupCost bits (List.replicate bounded true)+1+(3+1+(bounded+1)))),?_,result⟩
  have lookupBound := Lookup.lookupCost_le bits (List.replicate bounded true)
  simp only [List.length_replicate] at lookupBound
  have boundedLength : bounded≤bits.length := Nat.min_le_right _ _
  have cube : bits.length+(store (w 0)).length+1 ≤ (bits.length+(store (w 0)).length+1)^3 :=
    Nat.le_self_pow (by decide) _
  have budgetEq : copied ((lookupCountRoles extra w) 10)=bits := by simp [copied,lookupCountRoles]
  rw [budgetEq] at countBound
  rw [←header] at countBound
  change _≤100*(bits.length+(store (w 0)).length+1)^3
  omega

end Counting.External.SATVerification
