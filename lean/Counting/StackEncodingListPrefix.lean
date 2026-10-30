import Counting.StackEncodingListHeader
import Counting.StackEncodingListLoop

namespace Counting.StackMachine.EncodingPrograms

set_option backward.isDefEq.respectTransparency false

def listBodyRoles (extra : Nat) (w : FullListWorkspace extra) : ListWorkspace (extra+9) where
  toFun i := w (![0,7,8,1,9,10,6,4] i)
  inj' := by
    intro a b same
    have eq:=w.injective same
    fin_cases a <;> fin_cases b <;> simp_all

def listPrefixRoutine (extra : Nat) (w : FullListWorkspace extra) : Routine (extra+15) :=
  Routine.sequence (listHeaderRoutine extra w)
    (Routine.sequence (listLoop (extra+9) (listBodyRoles extra w))
      (Routine.sequence (Routine.ofProgram (ListPrograms.reverseProgram (extra+15) (w 6) (w 2)))
        (Routine.clear (w 3))))

def listPrefixStore (extra : Nat) (w : FullListWorkspace extra)
    (base : Fin (extra+17) → List Bool) : Fin (extra+17) → List Bool :=
  fun r => if r=w 0 then (listScan (base (w 0))).suffix
    else if r=w 1 then (listScan (base (w 0))).accepted::base (w 1)
    else if r=w 2 then (listScan (base (w 0))).reversed.reverse else base r

/-- A compositional parser of a canonical natural list. It returns the
unconsumed suffix, the serialized item fields, and an explicit Boolean flag;
all workspace is restored and unrelated registers retain their contents. -/
theorem listPrefix_executes (extra : Nat) (w : FullListWorkspace extra)
    (store : Fin (extra+17) → List Bool)
    (empty : ∀ i : Fin 17, i≠0 → i≠1 → store (w i)=[]) :
    ∃ time ≤ 1900*((store (w 0)).length+1)^3,
      Routine.Executes (listPrefixRoutine extra w) store time (listPrefixStore extra w store) := by
  have ne (i j : Fin 17) (h : i≠j) : w i≠w j := fun eq => h (w.injective eq)
  let input := store (w 0)
  let headerState := listHeaderStore extra w store
  have headerEmpty (i : Fin 17) (member : i∈({2,3,4,5,8,11,12,13,14,15,16}:Finset (Fin 17))) : store (w i)=[] := by
    apply empty i
    · intro eq; subst i; exact (by decide : (0:Fin 17)∉({2,3,4,5,8,11,12,13,14,15,16}:Finset (Fin 17))) member
    · intro eq; subst i; exact (by decide : (1:Fin 17)∉({2,3,4,5,8,11,12,13,14,15,16}:Finset (Fin 17))) member
  obtain ⟨headerTime,headerBound,headerRun⟩:=listHeader_executes extra w store headerEmpty
  let roles := listBodyRoles extra w
  have work (i : Fin 8) (member : i∈({1,2,4,5}:Finset (Fin 8))) : headerState (roles i)=[] := by
    fin_cases i <;> simp only [Finset.mem_insert,Finset.mem_singleton] at member
    all_goals first | contradiction | simp [roles,listBodyRoles,headerState,listHeaderStore,w.injective.eq_iff,empty]
  have initial : listState (extra+9) roles headerState (unframeSuffix input) [] (listHeaderAccepted input)
      (store (w 1)) (List.replicate (listCount input) true)=headerState := by
    funext r
    by_cases a : r=w 0
    · subst r; simp [listState,roles,listBodyRoles,headerState,listHeaderStore,input]
    · by_cases b : r=w 1
      · subst r; simp [listState,roles,listBodyRoles,headerState,listHeaderStore,input,w.injective.eq_iff]
      · by_cases c : r=w 6
        · subst r; simp [listState,roles,listBodyRoles,headerState,listHeaderStore,w.injective.eq_iff,empty]
        · by_cases d : r=w 4
          · subst r; simp [listState,roles,listBodyRoles,headerState,listHeaderStore,input,w.injective.eq_iff]
          · simp [listState,roles,listBodyRoles,a,b,c,d]
  obtain ⟨loopTime,loopBound,loopRun⟩:=listLoop_executes (extra+9) roles headerState work
    (List.replicate (listCount input) true) (unframeSuffix input) [] (listHeaderAccepted input) (store (w 1)) input.length
    (unframe_suffix_length input)
  rw [initial] at loopRun
  simp only [List.length_replicate] at loopRun loopBound
  let scanned := listState (extra+9) roles headerState (listScan input).suffix (listScan input).reversed
    (listScan input).accepted (store (w 1)) []
  change Routine.Executes _ _ _ scanned at loopRun
  have revSource : scanned (w 6)=(listScan input).reversed := by simp [scanned,listState,roles,listBodyRoles,w.injective.eq_iff]
  have revTarget : scanned (w 2)=[] := by simp [scanned,listState,roles,listBodyRoles,headerState,listHeaderStore,w.injective.eq_iff,empty]
  have reversing := Routine.reverse_executes (extra+15) (w 6) (w 2) (ne 6 2 (by decide)) scanned
  rw [revSource,revTarget,List.append_nil] at reversing
  let reversed := Function.update (Function.update scanned (w 6) []) (w 2) (listScan input).reversed.reverse
  have clearing := Routine.clear_executes (w 3) reversed
  have oldHeader : reversed (w 3)=Encoding.frame (unframePayload input) := by
    simp [reversed,scanned,listState,roles,listBodyRoles,headerState,listHeaderStore,w.injective.eq_iff,input]
  rw [oldHeader] at clearing
  have final : Function.update reversed (w 3) []=listPrefixStore extra w store := by
    funext r
    by_cases a : r=w 3
    · subst r; simp [listPrefixStore,w.injective.eq_iff,empty]
    · by_cases b : r=w 6
      · subst r; simp [reversed,listPrefixStore,w.injective.eq_iff,empty]
      · by_cases c : r=w 4
        · subst r; simp [reversed,scanned,listState,roles,listBodyRoles,listPrefixStore,w.injective.eq_iff,empty]
        · by_cases d : r=w 0
          · subst r; simp [reversed,scanned,listState,roles,listBodyRoles,listPrefixStore,w.injective.eq_iff,input]
          · by_cases e : r=w 1
            · subst r; simp [reversed,scanned,listState,roles,listBodyRoles,listPrefixStore,w.injective.eq_iff,input]
            · by_cases f : r=w 2
              · subst r; simp [reversed,listPrefixStore,w.injective.eq_iff,input]
              · simp [reversed,scanned,listState,roles,listBodyRoles,headerState,listHeaderStore,listPrefixStore,
                  a,b,c,d,e,f]
  rw [final] at clearing
  have composed := headerRun.sequence (loopRun.sequence (reversing.sequence clearing))
  refine ⟨headerTime+1+(loopTime+1+(2*(listScan input).reversed.length+1+1+((Encoding.frame (unframePayload input)).length+1))),?_,composed⟩
  have countBound := (listCount_le input).trans (unframe_suffix_length input)
  have scanBound := (scanItems_lengths (listCount input) (unframeSuffix input) [] (listHeaderAccepted input)).2
  have suffixBound := unframe_suffix_length input
  have payloadBound := unframe_payload_length input
  have loopLimit : loopTime≤ input.length*(20*input.length+42)+1 := loopBound.trans (by gcongr)
  have reversedLimit : (listScan input).reversed.length≤ input.length*(2*input.length+1) := by
    apply scanBound.trans
    simp only [List.length_nil,Nat.zero_add]
    gcongr
  have cubic := Nat.le_self_pow (by decide : 3≠0) (input.length+1)
  have square : (input.length+1)^2≤(input.length+1)^3 := by nlinarith
  rw [Encoding.frame_length]
  change _≤1900*(input.length+1)^3
  change headerTime≤1800*(input.length+1)^3 at headerBound
  nlinarith

end Counting.StackMachine.EncodingPrograms
