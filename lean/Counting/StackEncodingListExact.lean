import Counting.StackEncodingListPrefix

namespace Counting.StackMachine.EncodingPrograms

set_option backward.isDefEq.respectTransparency false

def listExactRoutine (extra : Nat) (w : FullListWorkspace extra) : Routine (extra+15) :=
  Routine.sequence (listPrefixRoutine extra w)
    (Routine.sequence (Routine.ofProgram (Compare.equalityProgram (extra+15) (w 0) (w 8) (w 1)))
      (Routine.ofProgram (combineFlagsProgram (extra+15) (w 1))))

def listExactStore (extra : Nat) (w : FullListWorkspace extra)
    (base : Fin (extra+17) → List Bool) : Fin (extra+17) → List Bool :=
  fun r => if r=w 0 then []
    else if r=w 1 then listCheck (base (w 0))::base (w 1)
    else if r=w 2 then (listScan (base (w 0))).reversed.reverse else base r

/-- The exact validator also consumes any remaining suffix. It retains the
serialized parsed fields for callers while returning one explicit result bit. -/
theorem listExact_executes (extra : Nat) (w : FullListWorkspace extra)
    (store : Fin (extra+17) → List Bool)
    (empty : ∀ i : Fin 17, i≠0 → i≠1 → store (w i)=[]) :
    ∃ time ≤ 1920*((store (w 0)).length+1)^3,
      Routine.Executes (listExactRoutine extra w) store time (listExactStore extra w store) := by
  have ne (i j : Fin 17) (h : i≠j) : w i≠w j := fun eq => h (w.injective eq)
  let input := store (w 0)
  let parsed := listPrefixStore extra w store
  obtain ⟨prefixTime,prefixBound,prefixRun⟩:=listPrefix_executes extra w store empty
  have source : parsed (w 0)=(listScan input).suffix := by simp [parsed,listPrefixStore,input]
  have scratch : parsed (w 8)=[] := by simp [parsed,listPrefixStore,w.injective.eq_iff,empty]
  have status : parsed (w 1)=(listScan input).accepted::store (w 1) := by simp [parsed,listPrefixStore,w.injective.eq_iff,input]
  have comparing := Compare.equality_executes (extra+15) (w 0) (w 8) (w 1)
    (ne 0 8 (by decide)) (ne 0 1 (by decide)) (ne 8 1 (by decide)) parsed
  rw [source,scratch,status] at comparing
  let compared := Function.update (Function.update (Function.update parsed (w 0) []) (w 8) []) (w 1)
    (decide ((listScan input).suffix=[])::(listScan input).accepted::store (w 1))
  have combining := combineFlags_executes (extra+15) (w 1) compared (listScan input).accepted
    (decide ((listScan input).suffix=[])) (store (w 1)) (by simp [compared])
  have final : Function.update compared (w 1)
      (((listScan input).accepted && decide ((listScan input).suffix=[]))::store (w 1))=listExactStore extra w store := by
    funext r
    by_cases a : r=w 0
    · subst r; simp [compared,listExactStore,w.injective.eq_iff]
    · by_cases b : r=w 1
      · subst r; simp [listExactStore,w.injective.eq_iff,listCheck,input]
      · by_cases c : r=w 8
        · subst r; simp [compared,listExactStore,w.injective.eq_iff,empty]
        · simp [compared,parsed,listPrefixStore,listExactStore,a,b,c,input]
  rw [final] at combining
  have composed := prefixRun.sequence (comparing.sequence combining)
  refine ⟨prefixTime+1+(Compare.equalityCost (listScan input).suffix []+1+3),?_,composed⟩
  have suffix := (scanItems_lengths (listCount input) (unframeSuffix input) [] (listHeaderAccepted input)).1
  have suffixLimit : (listScan input).suffix.length ≤ input.length := suffix.trans (unframe_suffix_length input)
  have compareBound := Compare.equalityCost_le (listScan input).suffix []
  simp only [List.length_nil,Nat.add_zero] at compareBound
  have cubic := Nat.le_self_pow (by decide : 3≠0) (input.length+1)
  change prefixTime≤1900*(input.length+1)^3 at prefixBound
  change _≤1920*(input.length+1)^3
  omega

end Counting.StackMachine.EncodingPrograms
