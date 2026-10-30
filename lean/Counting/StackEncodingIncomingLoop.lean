import Counting.StackEncodingIncomingItem
import Counting.StackEncodingIncomingScan

namespace Counting.StackMachine.EncodingPrograms
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

def incomingScanStore (extra : Nat) (w : IncomingWorkspace extra) (store : Store (extra+8))
    (tail firstTail : List Bool) (result : IncomingScanResult) : Store (extra+8) :=
  Function.update (Function.update (Function.update (Function.update store (w 0) result.suffix)
    (w 1) (result.accepted::tail)) (w 7) result.previous) (w 9) (result.first::firstTail)

theorem incomingScanStore_overwrite (extra : Nat) (w : IncomingWorkspace extra) (store : Store (extra+8))
    (tail firstTail : List Bool) (a b : IncomingScanResult) :
    incomingScanStore extra w (incomingScanStore extra w store tail firstTail a) tail firstTail b=
      incomingScanStore extra w store tail firstTail b := by
  funext r
  by_cases h0 : r=w 0 <;> by_cases h1 : r=w 1 <;> by_cases h7 : r=w 7 <;> by_cases h9 : r=w 9 <;>
    simp [incomingScanStore,h0,h1,h7,h9]

theorem incomingScanStore_update_other (extra : Nat) (w : IncomingWorkspace extra)
    (counter : Fin (extra+10)) (different : ∀ i,counter≠w i) (store : Store (extra+8))
    (tail firstTail bits : List Bool) (result : IncomingScanResult) :
    Function.update (incomingScanStore extra w store tail firstTail result) counter bits=
      incomingScanStore extra w (Function.update store counter bits) tail firstTail result := by
  funext r
  by_cases h : r=counter
  · subst r; simp [incomingScanStore,different]
  · simp [incomingScanStore,Function.update_apply,h]

theorem incomingLoop_executes (extra : Nat) (w : IncomingWorkspace extra)
    (counter : Fin (extra+10)) (different : ∀ i,counter≠w i)
    (bits : List Bool) (store : Store (extra+8)) (accepted first : Bool) (tail firstTail : List Bool)
    (status : store (w 1)=accepted::tail) (firstStatus : store (w 9)=first::firstTail)
    (empty : ∀ i∈({2,3,4,5,6}:Finset (Fin 10)),store (w i)=[])
    (counterValue : store counter=bits) (limit : Nat)
    (inputBound : (store (w 0)).length≤limit) (previousBound : (store (w 7)).length≤limit) :
    ∃ time ≤ bits.length*(100*(2*limit+(store (w 8)).length+1)+2)+1,
      Executes (forEach counter (incomingItem extra w)) store time
        (incomingScanStore extra w (Function.update store counter []) tail firstTail
          (scanIncoming (store (w 8)) bits.length (store (w 0)) (store (w 7)) first accepted)) := by
  induction bits generalizing store accepted first with
  | nil =>
      have unchanged : incomingScanStore extra w (Function.update store counter []) tail firstTail
          (scanIncoming (store (w 8)) 0 (store (w 0)) (store (w 7)) first accepted)=store := by
        rw [←counterValue,Function.update_eq_self]
        funext r
        by_cases h9 : r=w 9
        · subst r; simp [incomingScanStore,scanIncoming,firstStatus]
        · by_cases h7 : r=w 7
          · subst r; simp [incomingScanStore,scanIncoming,h9]
          · by_cases h1 : r=w 1
            · subst r; simp [incomingScanStore,scanIncoming,h9,h7,status]
            · by_cases h0 : r=w 0 <;> simp [incomingScanStore,scanIncoming,h9,h7,h1,h0]
      obtain ⟨ran,halted⟩:=repeat_empty counter (incomingItem extra w) store counterValue
      exact ⟨1,by simp,⟨⟨1,store⟩,ran,halted,unchanged.symm⟩⟩
  | cons bit bits ih =>
      let consumed:=Function.update store counter bits
      have consumedAt (i : Fin 10) : consumed (w i)=store (w i) := by simp [consumed,Ne.symm (different i)]
      obtain ⟨bodyTime,bodyBound,finishBody,bodyRun,bodyHalt,bodyStore⟩:=incomingItem_executes extra w consumed
        accepted first tail firstTail (by rw [consumedAt];exact status) (by rw [consumedAt];exact firstStatus)
        (by intro i hi;rw [consumedAt];exact empty i hi)
      let parsed:=parsePair (store (w 0))
      let item:IncomingScanResult:=⟨parsed.suffix,parsed.first,false,
        accepted && incomingPayloadCheck (store (w 8)) (store (w 7)) first parsed⟩
      let middle:=incomingScanStore extra w consumed tail firstTail item
      have itemStore : incomingItemStore extra w consumed accepted first tail firstTail=middle := by
        simp only [incomingItemStore,consumedAt,middle,incomingScanStore,item,parsed]
      rw [itemStore] at bodyStore
      have next0 : middle (w 0)=parsed.suffix := by simp [middle,incomingScanStore,w.injective.eq_iff,item]
      have next7 : middle (w 7)=parsed.first := by simp [middle,incomingScanStore,w.injective.eq_iff,item]
      have next8 : middle (w 8)=store (w 8) := by simp [middle,incomingScanStore,w.injective.eq_iff,consumedAt]
      have nextStatus : middle (w 1)=item.accepted::tail := by simp [middle,incomingScanStore,w.injective.eq_iff]
      have nextFirst : middle (w 9)=false::firstTail := by simp [middle,incomingScanStore,item]
      have nextCounter : middle counter=bits := by simp [middle,incomingScanStore,different,consumed]
      have nextEmpty (i : Fin 10) (hi : i∈({2,3,4,5,6}:Finset (Fin 10))) : middle (w i)=[] := by
        have a : i≠0 ∧ i≠1 ∧ i≠7 ∧ i≠9 := by fin_cases i <;> simp_all
        simpa only [middle,incomingScanStore,Function.update_of_ne (w.injective.ne a.2.2.2),
          Function.update_of_ne (w.injective.ne a.2.2.1),Function.update_of_ne (w.injective.ne a.2.1),
          Function.update_of_ne (w.injective.ne a.1),consumedAt] using empty i hi
      have parsedBound:=parsePair_length_bound (store (w 0))
      change parsed.first.length+parsed.second.length+parsed.suffix.length≤(store (w 0)).length at parsedBound
      obtain ⟨tailTime,tailBound,finishTail,tailRun,tailHalt,tailStore⟩:=ih middle item.accepted false
        nextStatus nextFirst nextEmpty nextCounter (by rw [next0];omega) (by rw [next7];omega)
      have firstRun:=repeat_iteration counter (incomingItem extra w) store bit bits counterValue
        bodyTime finishBody bodyRun bodyHalt
      have combined : incomingScanStore extra w (Function.update middle counter []) tail firstTail
          (scanIncoming (middle (w 8)) bits.length (middle (w 0)) (middle (w 7)) false item.accepted)=
          incomingScanStore extra w (Function.update store counter []) tail firstTail
            (scanIncoming (store (w 8)) (bit::bits).length (store (w 0)) (store (w 7)) first accepted) := by
        rw [next0,next7,next8]
        change incomingScanStore extra w
          (Function.update (incomingScanStore extra w consumed tail firstTail item) counter []) tail firstTail _=_
        rw [incomingScanStore_update_other extra w counter different,
          incomingScanStore_overwrite]
        simp only [consumed,Function.update_idem,List.length_cons,scanIncoming,item,parsed]
      refine ⟨bodyTime+2+tailTime,?_,⟨finishTail,?_,tailHalt,tailStore.trans combined⟩⟩
      · simp only [consumedAt] at bodyBound
        rw [next8] at tailBound
        simp only [List.length_cons]
        have limited : bodyTime≤100*(2*limit+(store (w 8)).length+1) := by omega
        nlinarith
      · rw [Machine.run_add,firstRun,Option.bind_some,bodyStore]
        exact tailRun

end Counting.StackMachine.EncodingPrograms
