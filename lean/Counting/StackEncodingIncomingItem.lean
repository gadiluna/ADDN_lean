import Counting.StackEncodingIncomingOrder
import Counting.StackEncodingIncomingSpec

namespace Counting.StackMachine.EncodingPrograms
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

abbrev IncomingWorkspace (extra : Nat) := Fin 10 ↪ Fin (extra+10)

def incomingPairRoles (extra : Nat) (w : IncomingWorkspace extra) : Fin 5 → Fin (extra+10) :=
  fun i=>w (![0,2,3,4,1] i)

def incomingCanonicalRoles (extra : Nat) (w : IncomingWorkspace extra) : Fin 4 ↪ Fin (extra+10) :=
  ⟨fun i=>w (![2,1,5,4] i),fun a b h=>by
    have equal:=w.injective h; fin_cases a <;> fin_cases b <;> simp_all⟩

def incomingBoundRoles (extra : Nat) (w : IncomingWorkspace extra) : Fin 6 ↪ Fin (extra+10) :=
  ⟨fun i=>w (![8,2,1,5,6,4] i),fun a b h=>by
    have equal:=w.injective h; fin_cases a <;> fin_cases b <;> simp_all⟩

def incomingPreviousRoles (extra : Nat) (w : IncomingWorkspace extra) : Fin 7 ↪ Fin (extra+10) :=
  ⟨fun i=>w (![2,7,1,5,6,4,9] i),fun a b h=>by
    have equal:=w.injective h; fin_cases a <;> fin_cases b <;> simp_all⟩

/-- Read one pair of frames, validate both canonical payloads and all incoming
edge conditions, and retain the reference as the next predecessor. -/
def incomingItem (extra : Nat) (w : IncomingWorkspace extra) : Routine (extra+8) :=
  sequence (pairRoutine (extra+5) (incomingPairRoles extra w))
    (sequence (ofProgram (combineFlagsProgram (extra+8) (w 1)))
      (sequence (canonicalGuard (extra+6) (incomingCanonicalRoles extra w))
        (sequence (positiveGuard (extra+8) (w 3) (w 1))
          (sequence (strictGuard (extra+4) (incomingBoundRoles extra w))
            (sequence (incomingOrder (extra+3) (incomingPreviousRoles extra w))
              (sequence (clear (w 7))
                (sequence (ofProgram (ListPrograms.copyProgram (extra+7) (w 2) (w 7) (w 4)))
                  (clear (w 2)))))))))

def incomingItemStore (extra : Nat) (w : IncomingWorkspace extra) (store : Store (extra+8))
    (accepted first : Bool) (tail firstTail : List Bool) : Store (extra+8) :=
  let parsed:=parsePair (store (w 0))
  Function.update (Function.update (Function.update (Function.update store
    (w 0) parsed.suffix) (w 1)
      ((accepted && incomingPayloadCheck (store (w 8)) (store (w 7)) first parsed)::tail))
    (w 7) parsed.first) (w 9) (false::firstTail)

/-- All data-dependent work, including malformed frames, has linear cost in
current input and the two saved numeric operands. Work is restored and the
bound and every unrelated register are preserved. -/
theorem incomingItem_executes (extra : Nat) (w : IncomingWorkspace extra)
    (store : Store (extra+8)) (accepted first : Bool) (tail firstTail : List Bool)
    (status : store (w 1)=accepted::tail) (firstStatus : store (w 9)=first::firstTail)
    (empty : ∀ i∈({2,3,4,5,6}:Finset (Fin 10)),store (w i)=[]) :
    ∃ time ≤ 100*((store (w 0)).length+(store (w 7)).length+(store (w 8)).length+1),
      Executes (incomingItem extra w) store time (incomingItemStore extra w store accepted first tail firstTail) := by
  have ne (i j : Fin 10) (h : i≠j) : w i≠w j := fun eq=>h (w.injective eq)
  have e (i : Fin 10) (h : i∈({2,3,4,5,6}:Finset (Fin 10))) := empty i h
  let parsed:=parsePair (store (w 0))
  let s1:=Function.update (Function.update (Function.update (Function.update store
    (w 0) parsed.suffix) (w 2) parsed.first) (w 3) parsed.second) (w 1) (parsed.accepted::store (w 1))
  have pairInjective : Function.Injective (incomingPairRoles extra w) := by
    intro a b h
    have equal:=w.injective h
    fin_cases a <;> fin_cases b <;> simp_all [incomingPairRoles]
  obtain ⟨t1,b1,r1⟩:=pair_executes_spec (extra+5) (incomingPairRoles extra w) pairInjective store (e 4 (by decide))
  have result1 : pairExpected (extra+5) (incomingPairRoles extra w) store=s1 := by
    funext r
    by_cases a : r=w 0
    · subst r; simp [pairExpected,incomingPairRoles,s1,parsed,w.injective.eq_iff]
    · by_cases b : r=w 2
      · subst r; simp [pairExpected,incomingPairRoles,s1,parsed,w.injective.eq_iff,e 2 (by decide)]
      · by_cases c : r=w 3
        · subst r; simp [pairExpected,incomingPairRoles,s1,parsed,w.injective.eq_iff,e 3 (by decide)]
        · by_cases d : r=w 4
          · subst r; simp [pairExpected,incomingPairRoles,s1,w.injective.eq_iff,e 4 (by decide)]
          · by_cases f : r=w 1
            · subst r; simp [pairExpected,incomingPairRoles,s1,parsed,w.injective.eq_iff]
            · simp [pairExpected,incomingPairRoles,s1,a,b,c,d,f]
  rw [result1] at r1
  let s2:=Function.update s1 (w 1) ((accepted && parsed.accepted)::tail)
  have r2 : Executes (ofProgram (combineFlagsProgram (extra+8) (w 1))) s1 3 s2 :=
    combineFlags_executes (extra+8) (w 1) s1 accepted parsed.accepted tail (by simp [s1,status])
  let s3:=Function.update s2 (w 1) (((accepted && parsed.accepted) && canonicalPayload parsed.first)::tail)
  have r3 : Executes (canonicalGuard (extra+6) (incomingCanonicalRoles extra w)) s2
      (6*parsed.first.length+9) s3 := by
    have executed:=canonicalGuard_executes (extra+6) (incomingCanonicalRoles extra w) s2
      (accepted && parsed.accepted) tail (by simp [incomingCanonicalRoles,s2])
      (by simp [incomingCanonicalRoles,s2,s1,w.injective.eq_iff,e 5 (by decide)])
      (by simp [incomingCanonicalRoles,s2,s1,w.injective.eq_iff,e 4 (by decide)])
    simpa [incomingCanonicalRoles,s2,s1,w.injective.eq_iff,s3] using executed
  let s4:=Function.update (Function.update s3 (w 3) []) (w 1)
    ((((accepted && parsed.accepted) && canonicalPayload parsed.first) && lastPayloadBit false parsed.second)::tail)
  have r4 : Executes (positiveGuard (extra+8) (w 3) (w 1)) s3 (parsed.second.length+9) s4 := by
    have executed:=positiveGuard_executes (extra+8) (w 3) (w 1) (ne 3 1 (by decide)) s3
      ((accepted && parsed.accepted) && canonicalPayload parsed.first) tail (by simp [s3])
    simpa [s3,s2,s1,w.injective.eq_iff,s4] using executed
  let beforeBound:=((accepted && parsed.accepted) && canonicalPayload parsed.first) && lastPayloadBit false parsed.second
  let s5:=Function.update s4 (w 1)
    ((beforeBound && !Binary.compareBits true (store (w 8)) parsed.first)::tail)
  have r5 : Executes (strictGuard (extra+4) (incomingBoundRoles extra w)) s4
      (Binary.preservingCompareCost (store (w 8)) parsed.first+7) s5 := by
    have executed:=strictGuard_executes (extra+4) (incomingBoundRoles extra w) s4 beforeBound tail
      (by simp [incomingBoundRoles,s4,beforeBound])
      (by simp [incomingBoundRoles,s4,s3,s2,s1,w.injective.eq_iff,e 5 (by decide)])
      (by simp [incomingBoundRoles,s4,s3,s2,s1,w.injective.eq_iff,e 6 (by decide)])
      (by simp [incomingBoundRoles,s4,s3,s2,s1,w.injective.eq_iff,e 4 (by decide)])
    simpa [incomingBoundRoles,s4,s3,s2,s1,w.injective.eq_iff,s5] using executed
  let beforeOrder:=beforeBound && !Binary.compareBits true (store (w 8)) parsed.first
  obtain ⟨t6,b6,r6⟩:=incomingOrder_executes (extra+3) (incomingPreviousRoles extra w) s5 beforeOrder first tail firstTail
    (by simp [incomingPreviousRoles,s5,beforeOrder])
    (by simpa [incomingPreviousRoles,s5,s4,s3,s2,s1,w.injective.eq_iff] using firstStatus)
    (by simp [incomingPreviousRoles,s5,s4,s3,s2,s1,w.injective.eq_iff,e 5 (by decide)])
    (by simp [incomingPreviousRoles,s5,s4,s3,s2,s1,w.injective.eq_iff,e 6 (by decide)])
    (by simp [incomingPreviousRoles,s5,s4,s3,s2,s1,w.injective.eq_iff,e 4 (by decide)])
  let acceptedNext:=beforeOrder && (first || !Binary.compareBits true parsed.first (store (w 7)))
  let s6:=Function.update (Function.update s5 (w 1) (acceptedNext::tail)) (w 9) (false::firstTail)
  have r6' : Executes (incomingOrder (extra+3) (incomingPreviousRoles extra w)) s5 t6 s6 := by
    simpa [incomingPreviousRoles,s5,s4,s3,s2,s1,w.injective.eq_iff,s6,acceptedNext] using r6
  have bound6 : t6≤7*(parsed.first.length+(store (w 7)).length)+20 := by
    simpa [incomingPreviousRoles,s5,s4,s3,s2,s1,w.injective.eq_iff] using b6
  let s7:=Function.update s6 (w 7) []
  have r7 : Executes (clear (w 7)) s6 ((store (w 7)).length+1) s7 := by
    simpa [s6,s5,s4,s3,s2,s1,w.injective.eq_iff,s7] using clear_executes (w 7) s6
  let s8:=Function.update s7 (w 7) parsed.first
  have r8 : Executes (ofProgram (ListPrograms.copyProgram (extra+7) (w 2) (w 7) (w 4)))
      s7 (5*parsed.first.length+2) s8 := by
    have executed:=copy_executes (extra+7) (w 2) (w 7) (w 4) (ne 2 7 (by decide))
      (ne 2 4 (by decide)) (ne 7 4 (by decide)) s7
      (by simp [s7,s6,s5,s4,s3,s2,s1,w.injective.eq_iff,e 4 (by decide)])
    simpa [ListPrograms.copyProgram,s8,s7,s6,s5,s4,s3,s2,s1,w.injective.eq_iff] using executed
  have r9:=clear_executes (w 2) s8
  have current : s8 (w 2)=parsed.first := by simp [s8,s7,s6,s5,s4,s3,s2,s1,w.injective.eq_iff]
  rw [current] at r9
  have final : Function.update s8 (w 2) []=incomingItemStore extra w store accepted first tail firstTail := by
    funext r
    by_cases a : r=w 2
    · subst r; simp [incomingItemStore,w.injective.eq_iff,e 2 (by decide)]
    · by_cases b : r=w 3
      · subst r; simp [s8,s7,s6,s5,s4,incomingItemStore,w.injective.eq_iff,e 3 (by decide)]
      · by_cases c : r=w 7 <;> by_cases d : r=w 9 <;> by_cases f : r=w 1 <;>
          simp [s8,s7,s6,s5,s4,s3,s2,s1,incomingItemStore,parsed,acceptedNext,beforeOrder,beforeBound,
            incomingPayloadCheck,Bool.and_assoc,a,b,c,d,f,w.injective.eq_iff]

  rw [final] at r9
  have composed:=r1.sequence (r2.sequence (r3.sequence (r4.sequence (r5.sequence (r6'.sequence (r7.sequence (r8.sequence r9)))))))
  refine ⟨_,?_,composed⟩
  have parsedBound:=parsePair_length_bound (store (w 0))
  have compareBound:=Binary.preservingCompareCost_le (store (w 8)) parsed.first
  change parsed.first.length+parsed.second.length+parsed.suffix.length≤(store (w 0)).length at parsedBound
  change t1≤6*(store (w 0)).length+13 at b1
  omega

end Counting.StackMachine.EncodingPrograms
