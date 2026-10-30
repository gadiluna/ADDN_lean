import Counting.ExternalMatchingLiteralLoop
import Counting.ExternalSATHeader

namespace Counting.External.MatchingMachine
open StackMachine StackMachine.Routine StackMachine.EncodingPrograms SATVerification
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

def generateClause (extra : Nat) (w : LiteralWorkspace extra) : Routine (extra+46) :=
  sequence (readListHeader (extra+31) (satHeaderRoles (extra+16) w.reader 1))
    (sequence (generateLiteralLoop extra w) (pushBit (w 35) true))

def generateClauseScratch : List (Fin 48) := generateLiteralScratch++[13,14,24]

def matchingClauseResult (extra : Nat) (w : LiteralWorkspace extra) (store : Fin (extra+48) → List Bool)
    (first width shift occurrence : Nat) (literals : List (Nat×Bool)) (suffix : List Bool) :=
  Function.update (Function.update (Function.update (Function.update store (w 0) suffix)
    (w 34) (List.replicate (occurrence+literals.length) true)) (w 35) (true::store (w 35)))
    (w 36) ((Encoding.sequence (Encoding.list Encoding.natural)
      (literalRows first width shift occurrence literals)).reverse++store (w 36))

theorem generateClause_executes (extra : Nat) (w : LiteralWorkspace extra)
    (literals : List (Nat×Bool)) (n width shift first bound occurrence : Nat)
    (store : Fin (extra+48) → List Bool) (accepted : Bool) (suffix tail : List Bool)
    (three : literals.length=3)
    (source : store (w 0)=(Encoding.list (Encoding.product Encoding.natural Encoding.boolean)).encode literals++suffix)
    (status : store (w 1)=accepted::tail) (nValue : (store (w 17)).length=n)
    (widthValue : store (w 32)=List.replicate width true) (shiftValue : store (w 33)=List.replicate shift true)
    (occurrenceValue : store (w 34)=List.replicate occurrence true) (firstValue : (store (w 35)).length=first)
    (sourceBound : (store (w 0)).length ≤ bound) (hn : n ≤ bound) (hw : width ≤ bound)
    (hs : shift ≤ bound) (hf : first ≤ bound) (ho : occurrence+3 ≤ bound)
    (fits : ∀ literal∈literals,literal.1 ≤ n)
    (empty : ∀ i∈generateClauseScratch,store (w i)=[]) :
    ∃ time ≤ 26000*(bound+1)^4,
      Executes (generateClause extra w) store time
        (matchingClauseResult extra w store first width shift occurrence literals suffix) := by
  let prepared := Function.update (Function.update store (w 0)
    (Encoding.sequence (Encoding.product Encoding.natural Encoding.boolean) literals++suffix))
    (w 24) (List.replicate literals.length true)
  have headerEmpty (i : Fin 17) (member : i∈({2,3,4,5,8,11,12,13,14,15,16}:Finset (Fin 17))) :
      store ((satHeaderRoles (extra+16) w.reader 1) i)=[] := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp [satHeaderRoles,headerPositions,LiteralWorkspace.reader,empty,generateClauseScratch,generateLiteralScratch]
  have positive (literal : Nat×Bool) : 0<((Encoding.product Encoding.natural Encoding.boolean).encode literal).length := by
    simp [Encoding.product,Encoding.boolean]
  obtain ⟨headerTime,headerBound,headerRun⟩ := readListHeader_canonical (extra+31) (satHeaderRoles (extra+16) w.reader 1)
    store accepted tail status headerEmpty (Encoding.product Encoding.natural Encoding.boolean) positive literals suffix source
  change Executes (readListHeader (extra+31) (satHeaderRoles (extra+16) w.reader 1)) store headerTime prepared at headerRun
  have preparedBound : (prepared (w 0)).length ≤ bound := by
    simp only [prepared,Function.update_of_ne (w.injective.ne (by decide : (0:Fin 48)≠24)),Function.update_self]
    rw [source] at sourceBound
    simp only [Encoding.list,List.length_append] at sourceBound ⊢
    omega
  have loopEmpty (i : Fin 48) (member : i∈generateLiteralScratch) : prepared (w i)=[] := by
    have a : i≠0 := by intro same;subst i;simp [generateLiteralScratch] at member
    have b : i≠24 := by intro same;subst i;simp [generateLiteralScratch] at member
    simpa [prepared,w.injective.eq_iff,a,b] using empty i (by simp [generateClauseScratch,member])
  obtain ⟨loopTime,loopBound,loopRun⟩ := generateLiteralLoop_executes extra w literals n width shift first bound occurrence prepared accepted suffix tail
    (by simp [prepared,w.injective.eq_iff]) (by simp [prepared])
    (by simp [prepared,w.injective.eq_iff,status]) (by simpa [prepared,w.injective.eq_iff] using nValue)
    (by simp [prepared,w.injective.eq_iff,widthValue]) (by simp [prepared,w.injective.eq_iff,shiftValue])
    (by simp [prepared,w.injective.eq_iff,occurrenceValue]) (by simpa [prepared,w.injective.eq_iff] using firstValue)
    preparedBound hn hw hs hf (by simpa only [three] using ho) fits loopEmpty
  let looped := literalLoopResult extra w prepared first width shift occurrence literals suffix
  have increment := pushBit_executes (w 35) true looped
  have final : Function.update looped (w 35) (true::looped (w 35))=
      matchingClauseResult extra w store first width shift occurrence literals suffix := by
    funext r
    by_cases a24 : r=w 24
    · subst r;simp [looped,literalLoopResult,matchingClauseResult,w.injective.eq_iff,empty,generateClauseScratch]
    · by_cases a35 : r=w 35
      · subst r;simp [looped,literalLoopResult,matchingClauseResult,prepared,w.injective.eq_iff]
      · by_cases a0 : r=w 0
        · subst r;simp [looped,literalLoopResult,matchingClauseResult,w.injective.eq_iff]
        · simp [looped,literalLoopResult,matchingClauseResult,prepared,a24,a35,a0,Function.update_apply]
  rw [final] at increment
  have composed := headerRun.sequence (loopRun.sequence increment)
  refine ⟨headerTime+1+(loopTime+1+1),?_,composed⟩
  have headerLimit : headerTime ≤ 1820*(bound+1)^4 := by
    apply headerBound.trans
    apply Nat.mul_le_mul_left
    exact (Nat.pow_le_pow_left (by omega : (store (w 0)).length+1 ≤ bound+1) 3).trans
      (Nat.pow_le_pow_right (by omega) (by decide))
  rw [three] at loopBound
  have one : 1 ≤ (bound+1)^4 := Nat.one_le_pow _ _ (by omega)
  omega

end Counting.External.MatchingMachine
