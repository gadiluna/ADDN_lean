import Counting.StackEncodingListCheck
import Counting.StackEncodingBoundedCount

namespace Counting.StackMachine.EncodingPrograms

set_option backward.isDefEq.respectTransparency false

abbrev FullListWorkspace (extra : Nat) := Fin 17 ↪ Fin (extra+17)

def listCountRoles (extra : Nat) (w : FullListWorkspace extra) : CountWorkspace (extra+6) where
  toFun i := w (![3,4,11,12,13,8,1,14,15,16,5] i)
  inj' := by
    intro a b same
    have eq := w.injective same
    fin_cases a <;> fin_cases b <;> simp_all

def listHeaderRoutine (extra : Nat) (w : FullListWorkspace extra) : Routine (extra+15) :=
  Routine.sequence (Routine.ofProgram (flaggedProgram (extra+13) (w 0) (w 2) (w 8) (w 1)))
    (Routine.sequence (frameRoutine (extra+14) (w 2) (w 3) (w 8))
      (Routine.sequence (Routine.ofProgram (ListPrograms.copyProgram (extra+14) (w 0) (w 5) (w 8)))
        (Routine.sequence (boundedCount (extra+6) (listCountRoles extra w))
          (Routine.ofProgram (combineFlagsProgram (extra+15) (w 1))))))

def listHeaderStore (extra : Nat) (w : FullListWorkspace extra)
    (base : Fin (extra+17) → List Bool) : Fin (extra+17) → List Bool :=
  fun r => if r=w 0 then unframeSuffix (base (w 0))
    else if r=w 1 then listHeaderAccepted (base (w 0))::base (w 1)
    else if r=w 3 then Encoding.frame (unframePayload (base (w 0)))
    else if r=w 4 then List.replicate (listCount (base (w 0))) true else base r

/-- Parse a length header and convert it to unary using the remaining input
as an explicit budget. Work registers are restored on both success and failure. -/
theorem listHeader_executes (extra : Nat) (w : FullListWorkspace extra)
    (store : Fin (extra+17) → List Bool)
    (empty : ∀ i : Fin 17, i∈({2,3,4,5,8,11,12,13,14,15,16}:Finset (Fin 17)) → store (w i)=[]) :
    ∃ time ≤ 1800*((store (w 0)).length+1)^3,
      Routine.Executes (listHeaderRoutine extra w) store time (listHeaderStore extra w store) := by
  have ne (i j : Fin 17) (h : i≠j) : w i≠w j := fun eq => h (w.injective eq)
  let input := store (w 0)
  let header := unframePayload input
  let suffix := unframeSuffix input
  let ok := (Encoding.unframe input).isSome
  let parsed := Function.update (Function.update (Function.update store (w 0) suffix) (w 2) header) (w 1) (ok::store (w 1))
  obtain ⟨parseTime,parseBound,parsing⟩ := flagged_executes (extra+13) (w 0) (w 2) (w 8) (w 1)
    (ne 0 2 (by decide)) (ne 0 8 (by decide)) (ne 2 8 (by decide))
    (ne 1 0 (by decide)) (ne 1 2 (by decide)) (ne 1 8 (by decide)) store (empty 8 (by decide))
  have parsedEq : flaggedResult (extra+13) (w 0) (w 2) (w 8) (w 1) store=parsed := by
    rw [flagged_result_updates (extra+13) (w 0) (w 2) (w 8) (w 1)
      (ne 0 2 (by decide)) (ne 0 8 (by decide)) (ne 2 8 (by decide))
      (ne 1 0 (by decide)) (ne 1 2 (by decide)) (ne 1 8 (by decide)) store (empty 8 (by decide)),empty 2 (by decide),List.append_nil]
  rw [parsedEq] at parsing
  have framing := frame_executes_updates (extra+14) (w 2) (w 3) (w 8)
    (ne 2 3 (by decide)) (ne 2 8 (by decide)) (ne 3 8 (by decide)) parsed
    (by simp [parsed,w.injective.eq_iff,empty 8 (by decide)])
  have cleared : Function.update parsed (w 2) []=
      Function.update (Function.update store (w 0) suffix) (w 1) (ok::store (w 1)) := by
    funext r
    by_cases same : r=w 2
    · subst r; simp [parsed,w.injective.eq_iff,empty 2 (by decide)]
    · simp [parsed,Function.update_apply,same]
  let framed := Function.update (Function.update (Function.update store (w 0) suffix) (w 1) (ok::store (w 1))) (w 3) (Encoding.frame header)
  have framedRun : Routine.Executes (frameRoutine (extra+14) (w 2) (w 3) (w 8)) parsed (5*header.length+4) framed := by
    have p2 : parsed (w 2)=header := by simp [parsed,w.injective.eq_iff]
    have p3 : parsed (w 3)=[] := by simp [parsed,w.injective.eq_iff,empty 3 (by decide)]
    simpa only [p2,p3,List.append_nil,cleared] using framing
  have copying := Routine.copy_executes (extra+14) (w 0) (w 5) (w 8)
    (ne 0 5 (by decide)) (ne 0 8 (by decide)) (ne 5 8 (by decide)) framed
    (by simp [framed,w.injective.eq_iff,empty 8 (by decide)])
  let copied := Function.update framed (w 5) suffix
  have copiedRun : Routine.Executes (Routine.ofProgram (ListPrograms.copyProgram (extra+14) (w 0) (w 5) (w 8)))
      framed (5*suffix.length+2) copied := by
    simpa only [framed,Function.update_of_ne (ne 0 3 (by decide)),Function.update_of_ne (ne 0 1 (by decide)),Function.update_self,
      Function.update_of_ne (ne 5 3 (by decide)),Function.update_of_ne (ne 5 1 (by decide)),
      Function.update_of_ne (ne 5 0 (by decide)),empty 5 (by decide),List.append_nil] using copying
  let roles := listCountRoles extra w
  have countStart : countState (extra+6) roles framed header 0 suffix=copied := by
    funext r
    by_cases a : r=w 3
    · subst r; simp [countState,roles,listCountRoles,framed,copied,w.injective.eq_iff]
    · by_cases b : r=w 4
      · subst r; simp [countState,roles,listCountRoles,framed,copied,w.injective.eq_iff,empty 4 (by decide)]
      · by_cases c : r=w 5
        · subst r; simp [countState,roles,listCountRoles,framed,copied,w.injective.eq_iff]
        · simp [countState,roles,listCountRoles,copied,a,b,c]
  have countEmpty (i : Fin 11) (member : i∈({2,3,4,5,7,8,9}:Finset (Fin 11))) : framed (roles i)=[] := by
    fin_cases i <;> simp only [Finset.mem_insert,Finset.mem_singleton] at member
    all_goals first | contradiction | simp [roles,listCountRoles,framed,w.injective.eq_iff,empty]
  obtain ⟨countTime,countBound,counting⟩:=boundedCount_executes (extra+6) roles framed header suffix countEmpty
  rw [countStart] at counting
  let counted := boundedCountResult (extra+6) roles framed header suffix
  let countOk := decide (Encoding.frame header=Encoding.natural.encode (listCount input))
  have countedStatus : counted (w 1)=countOk::ok::store (w 1) := by
    simp [counted,boundedCountResult,roles,listCountRoles,framed,w.injective.eq_iff,countOk,listCount,header,suffix,input]
  have combining := combineFlags_executes (extra+15) (w 1) counted ok countOk (store (w 1)) countedStatus
  have final : Function.update counted (w 1) ((ok && countOk)::store (w 1))=listHeaderStore extra w store := by
    funext r
    by_cases a : r=w 1
    · subst r; simp [listHeaderStore,w.injective.eq_iff,listHeaderAccepted,ok,countOk,input,header]
    · by_cases b : r=w 3
      · subst r; simp [counted,boundedCountResult,countState,roles,listCountRoles,framed,listHeaderStore,
          w.injective.eq_iff,header,input]
      · by_cases c : r=w 4
        · subst r; simp [counted,boundedCountResult,countState,roles,listCountRoles,framed,listHeaderStore,
            w.injective.eq_iff,listCount,header,suffix,input]
        · by_cases d : r=w 5
          · subst r; simp [counted,boundedCountResult,countState,roles,listCountRoles,framed,listHeaderStore,
              w.injective.eq_iff,empty 5 (by decide)]
          · simp [counted,boundedCountResult,countState,roles,listCountRoles,framed,listHeaderStore,
              Function.update_apply,a,b,c,d,header,suffix,input]
  rw [final] at combining
  have composed := parsing.sequence (framedRun.sequence (copiedRun.sequence (counting.sequence combining)))
  refine ⟨parseTime+1+(5*header.length+4+1+(5*suffix.length+2+1+(countTime+1+3))),?_,composed⟩
  have hp := unframe_payload_length input
  have hs := unframe_suffix_length input
  have cubic : countTime≤1728*(input.length+1)^3 := by
    apply countBound.trans
    rw [Encoding.frame_length]
    have inside : suffix.length+(2*header.length+1)+1≤3*(input.length+1) := by
      change header.length≤ input.length at hp
      change suffix.length≤ input.length at hs
      omega
    calc
      _ ≤ 64*(3*(input.length+1))^3 := by gcongr
      _ = _ := by ring
  have linear := Nat.le_self_pow (by decide : 3≠0) (input.length+1)
  change header.length≤ input.length at hp
  change suffix.length≤ input.length at hs
  change parseTime≤3*input.length+4 at parseBound
  change _≤1800*(input.length+1)^3
  omega

end Counting.StackMachine.EncodingPrograms
