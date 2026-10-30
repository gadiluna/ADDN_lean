import Counting.StackFrameReadPreserving
import Counting.StackRoutineFixedPrefix

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

/-- The natural-list header is skipped by a charged unary increment. The
presence bit is consumed after the read: the compact verifier uses zero for
an absent weight, while retaining its own separate dimension check. -/
def weightLookup (extra : Nat) (roles : Fin 8 ↪ Fin (extra+8)) : Routine (extra+6) :=
  sequence (pushBit (roles 1) true)
    (sequence (FieldAccess.preservingRead extra roles)
      (sequence (discardBit (roles 1)) (discardBit (roles 3))))

theorem weightLookup_executes (extra : Nat) (roles : Fin 8 ↪ Fin (extra+8))
    (store : Store (extra+6)) (values : List Nat)
    (input : store (roles 0)=(Encoding.list Encoding.natural).encode values)
    (e4 : store (roles 4)=[]) (e5 : store (roles 5)=[]) (e6 : store (roles 6)=[]) (e7 : store (roles 7)=[]) :
    ∃ time ≤ 10*(store (roles 0)).length+8*(store (roles 1)).length+28,
      Executes (weightLookup extra roles) store time
        (Function.update store (roles 2)
          ((values[(store (roles 1)).length]?.getD 0).bits++store (roles 2))) := by
  have different (i j : Fin 8) (ne : i≠j) : roles i≠roles j := fun same => ne (roles.injective same)
  have pushing := pushBit_executes (roles 1) true store
  let prepared := Function.update store (roles 1) (true::store (roles 1))
  obtain ⟨readTime,readBound,reading⟩ := FieldAccess.preservingRead_executes extra roles prepared
    (by simp [prepared,different 4 1 (by decide),e4])
    (by simp [prepared,different 5 1 (by decide),e5])
    (by simp [prepared,different 6 1 (by decide),e6])
    (by simp [prepared,different 7 1 (by decide),e7])
  have source : prepared (roles 0)=store (roles 0) := by simp [prepared,different 0 1 (by decide)]
  have index : prepared (roles 1)=true::store (roles 1) := by simp [prepared]
  have payload : prepared (roles 2)=store (roles 2) := by simp [prepared,different 2 1 (by decide)]
  have flag : prepared (roles 3)=store (roles 3) := by simp [prepared,different 3 1 (by decide)]
  rw [source,index] at reading readBound
  rw [payload,flag] at reading
  simp only [List.length_cons] at reading readBound
  have selected := FieldAccess.selectPayload_naturalList values (store (roles 1)).length
  rw [input,selected] at reading
  have bits : ((values[(store (roles 1)).length]?).map Nat.bits).getD []=
      ((values[(store (roles 1)).length]?).getD 0).bits := by
    cases found : values[(store (roles 1)).length]? <;> simp [Nat.zero_bits]
  rw [bits] at reading
  let resultBits := (values[(store (roles 1)).length]?.getD 0).bits
  let found := (values[(store (roles 1)).length]?).isSome
  have presence : ((values[(store (roles 1)).length]?).map Nat.bits).isSome=found := by
    simp [found]
  rw [presence] at reading
  let read := Function.update (Function.update prepared (roles 2) (resultBits++store (roles 2)))
    (roles 3) (found::store (roles 3))
  have discardIndex := discardBit_executes (roles 1) read
  have readIndex : read (roles 1)=true::store (roles 1) := by
    simp [read,prepared,different 1 2 (by decide),different 1 3 (by decide)]
  rw [readIndex,List.tail_cons] at discardIndex
  let restored := Function.update read (roles 1) (store (roles 1))
  have discardFlag := discardBit_executes (roles 3) restored
  have readFlag : restored (roles 3)=found::store (roles 3) := by
    simp [restored,read,different 3 1 (by decide)]
  rw [readFlag,List.tail_cons] at discardFlag
  have final : Function.update restored (roles 3) (store (roles 3))=
      Function.update store (roles 2) (resultBits++store (roles 2)) := by
    funext r
    by_cases at1 : r=roles 1
    · subst r;simp [restored,read,prepared,different 1 2 (by decide),different 1 3 (by decide)]
    · by_cases at2 : r=roles 2
      · subst r;simp [restored,read,prepared,different 2 1 (by decide),different 2 3 (by decide)]
      · by_cases at3 : r=roles 3
        · subst r;simp [restored,read,prepared,different 3 2 (by decide)]
        · simp [restored,read,prepared,at1,at2,at3]
  rw [final] at discardFlag
  have execution := pushing.sequence (reading.sequence (discardIndex.sequence discardFlag))
  exact ⟨_,by omega,execution⟩

end Counting.StackMachine.RealizabilityCheck
