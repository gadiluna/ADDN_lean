import Counting.StackEncodingParserLoop
import Counting.StackEncodingListHeader

namespace Counting.StackMachine.EncodingPrograms

set_option backward.isDefEq.respectTransparency false

def listHeaderWork (extra : Nat) (w : FullListWorkspace extra) : Finset (Fin (extra+17)) :=
  {w 2,w 3,w 4,w 5,w 8,w 11,w 12,w 13,w 14,w 15,w 16}

def headerEffect (input : List Bool) : ParseEffect :=
  ⟨unframeSuffix input,Encoding.frame (unframePayload input),listHeaderAccepted input⟩

def listPrepare (extra : Nat) (w : FullListWorkspace extra) : Routine (extra+15) :=
  Routine.sequence (listHeaderRoutine extra w)
    (Routine.sequence (Routine.ofProgram (combineFlagsProgram (extra+15) (w 1)))
      (Routine.ofProgram (ListPrograms.reverseProgram (extra+15) (w 3) (w 6))))

/-- Preparing a generic list retains the bounded unary counter, merges the
header flag with the caller's flag, and appends the actual header to the
reversed output. All other header scratch is restored. -/
theorem listPrepare_executes (extra : Nat) (w : FullListWorkspace extra)
    (store : Fin (extra+17) → List Bool) (accepted : Bool) (tail : List Bool)
    (status : store (w 1)=accepted::tail)
    (empty : ∀ r∈listHeaderWork extra w,store r=[]) :
    ∃ time ≤ 1810*((store (w 0)).length+1)^3,
      Routine.Executes (listPrepare extra w) store time
        (Function.update (parseStore (w 0) (w 1) (w 6) store accepted tail (headerEffect (store (w 0))))
          (w 4) (List.replicate (listCount (store (w 0))) true)) := by
  have ne (i j : Fin 17) (h : i≠j) : w i≠w j := fun eq => h (w.injective eq)
  have baseEmpty (i : Fin 17) (member : i∈({2,3,4,5,8,11,12,13,14,15,16}:Finset (Fin 17))) : store (w i)=[] := by
    apply empty
    simp only [Finset.mem_insert,Finset.mem_singleton] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp [listHeaderWork]
  obtain ⟨headerTime,headerBound,headerRun⟩:=listHeader_executes extra w store baseEmpty
  let input:=store (w 0)
  let headerState:=listHeaderStore extra w store
  have headStatus : headerState (w 1)=listHeaderAccepted input::accepted::tail := by
    simp [headerState,listHeaderStore,w.injective.eq_iff,input,status]
  have combining:=combineFlags_executes (extra+15) (w 1) headerState accepted (listHeaderAccepted input) tail headStatus
  let combined:=Function.update headerState (w 1) ((accepted && listHeaderAccepted input)::tail)
  have source : combined (w 3)=Encoding.frame (unframePayload input) := by
    simp [combined,headerState,listHeaderStore,w.injective.eq_iff,input]
  have output : combined (w 6)=store (w 6) := by
    simp [combined,headerState,listHeaderStore,w.injective.eq_iff]
  have reversing:=Routine.reverse_executes (extra+15) (w 3) (w 6) (ne 3 6 (by decide)) combined
  rw [source,output] at reversing
  have result : Function.update (Function.update combined (w 3) []) (w 6)
      ((Encoding.frame (unframePayload input)).reverse++store (w 6))=
      Function.update (parseStore (w 0) (w 1) (w 6) store accepted tail (headerEffect input))
        (w 4) (List.replicate (listCount input) true) := by
    funext r
    by_cases a : r=w 0
    · subst r; simp [combined,headerState,listHeaderStore,parseStore,headerEffect,w.injective.eq_iff,input]
    · by_cases b : r=w 1
      · subst r; simp [combined,parseStore,headerEffect,w.injective.eq_iff,input]
      · by_cases c : r=w 3
        · subst r; simp [parseStore,headerEffect,w.injective.eq_iff,baseEmpty 3 (by decide)]
        · by_cases d : r=w 4
          · subst r; simp [combined,headerState,listHeaderStore,w.injective.eq_iff,input]
          · by_cases e : r=w 6
            · subst r; simp [parseStore,headerEffect,w.injective.eq_iff]
            · simp [combined,headerState,listHeaderStore,parseStore,a,b,c,d,e]
  rw [result] at reversing
  have composed:=headerRun.sequence (combining.sequence reversing)
  refine ⟨headerTime+1+(3+1+(2*(Encoding.frame (unframePayload input)).length+1)),?_,composed⟩
  have payload:=unframe_payload_length input
  have cubic:=Nat.le_self_pow (by decide : 3≠0) (input.length+1)
  rw [Encoding.frame_length]
  change headerTime≤1800*(input.length+1)^3 at headerBound
  change _≤1810*(input.length+1)^3
  omega

end Counting.StackMachine.EncodingPrograms
