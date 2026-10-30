import Counting.StackEncodingIncomingLoop
import Counting.StackEncodingListHeader
import Counting.StackEncodingIncomingPrefixSpec

namespace Counting.StackMachine.EncodingPrograms
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

abbrev FullIncomingWorkspace (extra : Nat) := Fin 20 ↪ Fin (extra+20)

def incomingHeaderRoles (extra : Nat) (w : FullIncomingWorkspace extra) : FullListWorkspace (extra+3) :=
  ⟨fun i=>w ⟨i.val,by omega⟩,fun a b h=>Fin.ext (congrArg (fun i : Fin 20=>i.val) (w.injective h))⟩

def incomingBodyRoles (extra : Nat) (w : FullIncomingWorkspace extra) : IncomingWorkspace (extra+10) :=
  ⟨fun i=>w (![0,1,7,9,8,10,3,17,18,19] i),fun a b h=>by
    have equal:=w.injective h; fin_cases a <;> fin_cases b <;> simp_all⟩

def incomingPrefix (extra : Nat) (w : FullIncomingWorkspace extra) : Routine (extra+18) :=
  sequence (listHeaderRoutine (extra+3) (incomingHeaderRoles extra w))
    (sequence (ofProgram (combineFlagsProgram (extra+18) (w 1)))
      (sequence (clear (w 3)) (forEach (w 4) (incomingItem (extra+10) (incomingBodyRoles extra w)))))

theorem incomingPrefix_executes (extra : Nat) (w : FullIncomingWorkspace extra)
    (store : Store (extra+18)) (accepted first : Bool) (tail firstTail : List Bool)
    (status : store (w 1)=accepted::tail) (firstStatus : store (w 19)=first::firstTail)
    (empty : ∀ i : Fin 20,2≤ i.val → i.val≤16 → store (w i)=[]) :
    ∃ time ≤ 2500*((store (w 0)).length+(store (w 17)).length+(store (w 18)).length+1)^3,
      Executes (incomingPrefix extra w) store time
        (incomingScanStore (extra+10) (incomingBodyRoles extra w) store tail firstTail
          (incomingPrefixResult (store (w 18)) (store (w 0)) (store (w 17)) first accepted)) := by
  have ne (i j : Fin 20) (h : i≠j) : w i≠w j := fun eq=>h (w.injective eq)
  have headEmpty (i : Fin 17) (hi : i∈({2,3,4,5,8,11,12,13,14,15,16} : Finset (Fin 17))) :
      store (incomingHeaderRoles extra w i)=[] := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      apply empty <;> decide
  obtain ⟨t1,b1,r1⟩:=listHeader_executes (extra+3) (incomingHeaderRoles extra w) store headEmpty
  let s1:=listHeaderStore (extra+3) (incomingHeaderRoles extra w) store
  let input:=store (w 0)
  have h1 : s1 (w 1)=listHeaderAccepted input::accepted::tail := by
    simp [s1,listHeaderStore,incomingHeaderRoles,w.injective.eq_iff,input,status]
  have r2:=combineFlags_executes (extra+18) (w 1) s1 accepted (listHeaderAccepted input) tail h1
  let s2:=Function.update s1 (w 1) ((accepted && listHeaderAccepted input)::tail)
  have header : s2 (w 3)=Encoding.frame (unframePayload input) := by
    simp [s2,s1,listHeaderStore,incomingHeaderRoles,w.injective.eq_iff,input]
  have r3:=clear_executes (w 3) s2
  rw [header] at r3
  let s3:=Function.update s2 (w 3) []
  have boundStore : s3 (w 18)=store (w 18) := by
    simp [s3,s2,s1,listHeaderStore,incomingHeaderRoles,w.injective.eq_iff]
  have previousStore : s3 (w 17)=store (w 17) := by
    simp [s3,s2,s1,listHeaderStore,incomingHeaderRoles,w.injective.eq_iff]
  have sourceStore : s3 (w 0)=unframeSuffix input := by
    simp [s3,s2,s1,listHeaderStore,incomingHeaderRoles,w.injective.eq_iff,input]
  have counterDistinct : ∀ i,w 4≠incomingBodyRoles extra w i := by
    intro i h
    have equal:=w.injective h
    fin_cases i <;> simp at equal
  have itemEmpty (i : Fin 10) (hi : i∈({2,3,4,5,6}:Finset (Fin 10))) :
      s3 (incomingBodyRoles extra w i)=[] := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl <;>
      simp [s3,s2,s1,listHeaderStore,incomingHeaderRoles,incomingBodyRoles,w.injective.eq_iff,empty]
  have sourceBound := unframe_suffix_length input
  obtain ⟨t4,b4,r4⟩:=incomingLoop_executes (extra+10) (incomingBodyRoles extra w) (w 4) counterDistinct
    (List.replicate (listCount input) true) s3 (accepted && listHeaderAccepted input) first tail firstTail
    (by simp [s3,s2,incomingBodyRoles,w.injective.eq_iff])
    (by simpa [s3,s2,s1,listHeaderStore,incomingHeaderRoles,incomingBodyRoles,w.injective.eq_iff] using firstStatus)
    itemEmpty
    (by simp [s3,s2,s1,listHeaderStore,incomingHeaderRoles,w.injective.eq_iff,input])
    (input.length+(store (w 17)).length)
    (by change (s3 (w 0)).length≤_;rw [sourceStore];omega)
    (by change (s3 (w 17)).length≤_;rw [previousStore];omega)
  simp only [List.length_replicate] at b4 r4
  change Executes (forEach (w 4) (incomingItem (extra+10) (incomingBodyRoles extra w))) s3 t4
    (incomingScanStore (extra+10) (incomingBodyRoles extra w) (Function.update s3 (w 4) []) tail firstTail
      (scanIncoming (s3 (w 18)) (listCount input) (s3 (w 0)) (s3 (w 17)) first
        (accepted && listHeaderAccepted input))) at r4
  rw [boundStore,sourceStore,previousStore] at r4
  have restoreAll (result : IncomingScanResult) :
      incomingScanStore (extra+10) (incomingBodyRoles extra w) (Function.update s3 (w 4) []) tail firstTail result=
      incomingScanStore (extra+10) (incomingBodyRoles extra w) store tail firstTail result := by
    funext r
    change (Function.update (Function.update (Function.update (Function.update
      (Function.update s3 (w 4) []) (w 0) result.suffix) (w 1) (result.accepted::tail))
      (w 17) result.previous) (w 19) (result.first::firstTail)) r =
      (Function.update (Function.update (Function.update (Function.update store
        (w 0) result.suffix) (w 1) (result.accepted::tail)) (w 17) result.previous)
        (w 19) (result.first::firstTail)) r
    dsimp only [s3,s2,s1,listHeaderStore]
    by_cases h0 : r=w 0 <;> by_cases h1' : r=w 1 <;> by_cases h3 : r=w 3 <;> by_cases h4 : r=w 4 <;>
      by_cases h17 : r=w 17 <;> by_cases h19 : r=w 19 <;>
      simp [listHeaderStore,incomingHeaderRoles,h0,h1',h3,h4,h17,h19,w.injective.eq_iff,empty]

  rw [restoreAll] at r4
  have composed:=r1.sequence (r2.sequence (r3.sequence r4))
  refine ⟨_,?_,composed⟩
  change t1≤1800*(input.length+1)^3 at b1
  change t4≤listCount input*(100*(2*(input.length+(store (w 17)).length)+(s3 (w 18)).length+1)+2)+1 at b4
  rw [boundStore] at b4
  have countBound:=(listCount_le input).trans sourceBound
  let Q:=input.length+(store (w 17)).length+(store (w 18)).length+1
  have cubic : (input.length+1)^3≤Q^3 := Nat.pow_le_pow_left (by omega) 3
  have square : Q^2≤Q^3 := Nat.pow_le_pow_right (by omega) (by decide)
  have linear : Q≤Q^3 := Nat.le_self_pow (by decide : 3≠0) Q
  have positiveQ : 1≤Q := by omega
  have oneInput : input.length≤Q := by omega
  have iterations : listCount input≤Q := by omega
  have perIteration : 100*(2*(input.length+(store (w 17)).length)+(store (w 18)).length+1)+2≤202*Q := by omega
  have product := Nat.mul_le_mul iterations perIteration
  have loop : t4≤202*Q^2+1 := by nlinarith
  have payload:=unframe_payload_length input
  rw [Encoding.frame_length]
  change _≤2500*Q^3
  have payloadQ : (unframePayload input).length≤Q := by omega
  nlinarith

end Counting.StackMachine.EncodingPrograms
