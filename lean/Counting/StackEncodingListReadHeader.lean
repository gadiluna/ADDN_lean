import Counting.StackEncodingListHeader
import Counting.StackRoutineBasic

/-! Read a list count, accumulate its status, and discard its serialized
header. This routine only validates the header; the bounded item loop must
still execute the element parser/checker. -/
namespace Counting.StackMachine.EncodingPrograms
open Routine
set_option backward.isDefEq.respectTransparency false

def readListHeader (extra : Nat) (w : FullListWorkspace extra) : Routine (extra+15) :=
  sequence (listHeaderRoutine extra w)
    (sequence (ofProgram (combineFlagsProgram (extra+15) (w 1))) (clear (w 3)))

def readListHeaderStore (extra : Nat) (w : FullListWorkspace extra) (store : Store (extra+15))
    (accepted : Bool) (tail : List Bool) : Store (extra+15) :=
  fun r=>if r=w 0 then unframeSuffix (store (w 0))
    else if r=w 1 then (accepted && listHeaderAccepted (store (w 0)))::tail
    else if r=w 4 then List.replicate (listCount (store (w 0))) true else store r

theorem readListHeader_executes (extra : Nat) (w : FullListWorkspace extra) (store : Store (extra+15))
    (accepted : Bool) (tail : List Bool) (statusEq : store (w 1)=accepted::tail)
    (empty : ∀ i : Fin 17,i∈({2,3,4,5,8,11,12,13,14,15,16}:Finset (Fin 17)) → store (w i)=[]) :
    ∃ time ≤ 1820*((store (w 0)).length+1)^3,
      Executes (readListHeader extra w) store time (readListHeaderStore extra w store accepted tail) := by
  have ne (i j : Fin 17) (h : i≠j) : w i≠w j:=fun equal=>h (w.injective equal)
  obtain ⟨headerTime,headerBound,headerRun⟩:=listHeader_executes extra w store empty
  let parsed:=listHeaderStore extra w store
  have nextStatus : parsed (w 1)=listHeaderAccepted (store (w 0))::accepted::tail := by
    simp [parsed,listHeaderStore,w.injective.eq_iff,statusEq]
  have combined:=combineFlags_executes (extra+15) (w 1) parsed accepted
    (listHeaderAccepted (store (w 0))) tail nextStatus
  let joined:=Function.update parsed (w 1) ((accepted && listHeaderAccepted (store (w 0)))::tail)
  have nextHeader : joined (w 3)=Encoding.frame (unframePayload (store (w 0))) := by
    simp [joined,parsed,listHeaderStore,w.injective.eq_iff]
  have clearing:=clear_executes (w 3) joined
  rw [nextHeader] at clearing
  have composed:=headerRun.sequence (combined.sequence clearing)
  have result : Function.update joined (w 3) []=readListHeaderStore extra w store accepted tail := by
    funext r
    by_cases r0 : r=w 0
    · subst r;simp [joined,parsed,listHeaderStore,readListHeaderStore,w.injective.eq_iff]
    · by_cases r1 : r=w 1
      · subst r;simp [joined,readListHeaderStore,w.injective.eq_iff]
      · by_cases r3 : r=w 3
        · subst r;simp [readListHeaderStore,w.injective.eq_iff,empty 3 (by decide)]
        · by_cases r4 : r=w 4
          · subst r;simp [joined,parsed,listHeaderStore,readListHeaderStore,w.injective.eq_iff]
          · simp [joined,parsed,listHeaderStore,readListHeaderStore,r0,r1,r3,r4]
  rw [result] at composed
  refine ⟨_,?_,composed⟩
  have headerLength:=unframe_payload_length (store (w 0))
  have linear : (store (w 0)).length+1≤((store (w 0)).length+1)^3:=Nat.le_self_pow (by decide) _
  rw [Encoding.frame_length]
  omega

theorem listHeader_natural {α : Type} (codec : Encoding.Codec α)
    (positive : ∀ value,0<(codec.encode value).length) (values : List α) (suffix : List Bool) :
    unframeSuffix ((Encoding.list codec).encode values++suffix)=Encoding.sequence codec values++suffix ∧
    listCount ((Encoding.list codec).encode values++suffix)=values.length ∧
    listHeaderAccepted ((Encoding.list codec).encode values++suffix)=true := by
  let input:=(Encoding.list codec).encode values++suffix
  have parsed : Encoding.unframe input=some (values.length.bits,Encoding.sequence codec values++suffix) := by
    change Encoding.unframe ((Encoding.frame values.length.bits++Encoding.sequence codec values)++suffix)=_
    rw [List.append_assoc,Encoding.unframe_frame]
  have sequenceBound : ∀ xs : List α,xs.length≤(Encoding.sequence codec xs).length := by
    intro xs
    induction xs with
    | nil=>rfl
    | cons value values ih=>
      have first:=positive value
      simp only [List.length_cons,Encoding.sequence,List.length_append]
      omega
  have countBound:=sequenceBound values
  have count : listCount input=values.length := by
    simp only [listCount,unframePayload,unframeSuffix,parsed,Option.map_some,Option.getD_some]
    rw [countRun_natural _ _ _ (by omega),Nat.zero_add,Nat.min_eq_right]
    simpa only [List.length_append] using countBound.trans (Nat.le_add_right _ _)
  have accepted : listHeaderAccepted input=true := by
    simp only [listHeaderAccepted,unframePayload,parsed,count,Option.map_some,Option.getD_some,Option.isSome_some]
    simp [Encoding.natural]
  refine ⟨?_,count,accepted⟩
  change unframeSuffix input=_
  simp only [unframeSuffix,parsed,Option.map_some,Option.getD_some]

theorem readListHeader_canonical (extra : Nat) (w : FullListWorkspace extra) (store : Store (extra+15))
    (accepted : Bool) (tail : List Bool) (statusEq : store (w 1)=accepted::tail)
    (empty : ∀ i : Fin 17,i∈({2,3,4,5,8,11,12,13,14,15,16}:Finset (Fin 17)) → store (w i)=[])
    {α : Type} (codec : Encoding.Codec α) (positive : ∀ value,0<(codec.encode value).length)
    (values : List α) (suffix : List Bool) (encoded : store (w 0)=(Encoding.list codec).encode values++suffix) :
    ∃ time ≤ 1820*((store (w 0)).length+1)^3,
      Executes (readListHeader extra w) store time
        (Function.update (Function.update store (w 0) (Encoding.sequence codec values++suffix))
          (w 4) (List.replicate values.length true)) := by
  obtain ⟨time,bounded,executed⟩:=readListHeader_executes extra w store accepted tail statusEq empty
  obtain ⟨rest,count,header⟩:=listHeader_natural codec positive values suffix
  have result : readListHeaderStore extra w store accepted tail=
      Function.update (Function.update store (w 0) (Encoding.sequence codec values++suffix))
        (w 4) (List.replicate values.length true) := by
    funext r
    by_cases r0 : r=w 0
    · subst r;simp [readListHeaderStore,w.injective.eq_iff,encoded,rest]
    · by_cases r1 : r=w 1
      · subst r;simp [readListHeaderStore,w.injective.eq_iff,encoded,header,statusEq]
      · by_cases r4 : r=w 4
        · subst r;simp [readListHeaderStore,w.injective.eq_iff,encoded,count]
        · simp [readListHeaderStore,r0,r1,r4]
  rw [result] at executed
  exact ⟨time,bounded,executed⟩

end Counting.StackMachine.EncodingPrograms
