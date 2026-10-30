import Counting.StackNetworkCertificateRead
import Counting.StackEncodingDagParser
import Counting.StackRoutineMove
import Counting.EncodingNetwork

namespace Counting.StackMachine.DagUpdate.Canonical
open Routine EncodingPrograms RealizabilityCall
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def initializeRead : Routine 128 := sequence (move 127 0 (context 25) 3)
  (sequence (pushBit (context 4) true) (NetworkCertificate.consumeField DagParser.nodes 25 20))

def initializeReadData (source : Executable.Vista) : Fin 30→List Bool :=
  Function.update (Function.update (Function.update (fun _=>[]) 4 [true])
    25 (Encoding.natural.encode source.bottom)) 20 ((Encoding.array Encoding.node).encode source.nodes)

def initializeReadBudget (source : Executable.Vista) : Nat :=
  Complexity.polynomial DagParser.nodes.coefficient DagParser.nodes.exponent (Encoding.vista.encode source).length+
    20*(Encoding.vista.encode source).length+20

theorem initializeRead_executes (source : Executable.Vista) :
    ∃ time ≤ initializeReadBudget source,
      Executes initializeRead (inputStore 128 (Encoding.vista.encode source)) time
        (file (initializeReadData source)) := by
  let word := Encoding.vista.encode source
  let data : Fin 30→List Bool := Function.update (fun _=>[]) 25 word
  have moving := move_executes 127 (0:Fin 130) (context 25) 3
    (by decide) (by decide) (by decide) (inputStore 128 word) rfl
  rw [show inputStore 128 word 0=word by rfl,
    show inputStore 128 word (context 25)=[] by rfl,List.append_nil] at moving
  have moved : Function.update (Function.update (inputStore 128 word) (context 25) word) 0 []=file data := by
    funext r
    by_cases h0:r=0
    · subst r;simp [file,context]
    · by_cases h25:r=context 25
      · subst r;simp [data,context,file]
      · have nd : ∀h:100 ≤ r.val,(⟨r.val-100,by omega⟩:Fin 30)≠25 := by
          intro h same
          apply h25
          apply Fin.ext
          have sameVal := congrArg Fin.val same
          change r.val-100=25 at sameVal
          change r.val=100+25
          omega
        simp [file,data,inputStore,h0,h25]
        intro h
        exact Function.update_of_ne (nd h) word (fun _=>[])
  rw [moved] at moving
  have flag := pushBit_executes (context 4) true (file data)
  rw [file_context,show data 4=[] by simp [data],file_update] at flag
  let ready := Function.update data 4 [true]
  obtain ⟨time,bound,read⟩ := NetworkCertificate.consumeField_executes DagParser.nodes ready 25 20
    (by decide) (by decide) (by decide) (by decide) (by decide)
    source.nodes.toList (Encoding.natural.encode source.bottom) true []
    (by rfl) (by simp [ready]) (by simp [ready,data]) (by simp [ready,data])
  have final : Function.update (Function.update ready 25 (Encoding.natural.encode source.bottom))
      20 ((Encoding.list Encoding.node).encode source.nodes.toList)=initializeReadData source := by
    funext r
    fin_cases r <;> simp [ready,data,initializeReadData,Encoding.array,Encoding.transport]
  rw [final] at read
  have encoded : ready 25=word := by simp [ready,data]
  rw [encoded] at bound
  exact ⟨_,by dsimp only [initializeReadBudget,word] at *;omega,moving.sequence (flag.sequence read)⟩

end Counting.StackMachine.DagUpdate.Canonical
