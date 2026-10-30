import Counting.StackNetworkCertificateRead
import Counting.NetworkRecognitionParser
import Counting.StackRoutineMove

namespace Counting.StackMachine.NetworkVista.Run
open Routine EncodingPrograms RealizabilityCall
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def initialRead : Routine 128 := sequence (move 127 0 (context 20) 3)
  (sequence (pushBit (context 4) true)
    (NetworkCertificate.consumeField NetworkRecognition.booleans 20 1))

def initialReadData (input : Simulation.Input) : Fin 30→List Bool :=
  Function.update (Function.update (Function.update (fun _=>[]) 4 [true])
    20 ((Encoding.array (Encoding.array (Encoding.array Encoding.natural))).encode input.rounds))
    1 ((Encoding.array Encoding.boolean).encode input.leaders)

def initialReadBudget (input : Simulation.Input) : Nat :=
  Complexity.polynomial NetworkRecognition.booleans.coefficient NetworkRecognition.booleans.exponent
    (Encoding.networkInput.encode input).length+20*(Encoding.networkInput.encode input).length+20

theorem initialRead_executes (input : Simulation.Input) :
    ∃ time ≤ initialReadBudget input,
      Executes initialRead (inputStore 128 (Encoding.networkInput.encode input)) time
        (file (initialReadData input)) := by
  let word := Encoding.networkInput.encode input
  let data : Fin 30→List Bool := Function.update (fun _=>[]) 20 word
  have moving := move_executes 127 (0:Fin 130) (context 20) 3
    (by decide) (by decide) (by decide) (inputStore 128 word) rfl
  rw [show inputStore 128 word 0=word by rfl,
    show inputStore 128 word (context 20)=[] by rfl,List.append_nil] at moving
  have moved : Function.update (Function.update (inputStore 128 word) (context 20) word) 0 []=file data := by
    funext r
    by_cases h0:r=0
    · subst r;simp [file,context]
    · by_cases h20:r=context 20
      · subst r;simp [data,context,file]
      · have nd : ∀h:100≤r.val,(⟨r.val-100,by omega⟩:Fin 30)≠20 := by
          intro h same
          apply h20
          apply Fin.ext
          have sameVal := congrArg Fin.val same
          change r.val-100=20 at sameVal
          change r.val=100+20
          omega
        simp [file,data,inputStore,h0,h20]
        intro h
        exact Function.update_of_ne (nd h) word (fun _=>[])
  rw [moved] at moving
  have flag := pushBit_executes (context 4) true (file data)
  rw [file_context,show data 4=[] by simp [data],file_update] at flag
  let ready := Function.update data 4 [true]
  obtain ⟨time,bound,read⟩ := NetworkCertificate.consumeField_executes NetworkRecognition.booleans
    ready 20 1 (by decide) (by decide) (by decide) (by decide) (by decide)
    input.leaders ((Encoding.array (Encoding.array (Encoding.array Encoding.natural))).encode input.rounds)
    true [] (by rfl) (by simp [ready]) (by simp [ready,data]) (by simp [ready,data])
  have final : Function.update (Function.update ready 20
      ((Encoding.array (Encoding.array (Encoding.array Encoding.natural))).encode input.rounds))
      1 ((Encoding.array Encoding.boolean).encode input.leaders)=initialReadData input := by
    funext r
    fin_cases r <;> simp [ready,data,initialReadData]
  rw [final] at read
  have source : ready 20=word := by simp [ready,data]
  rw [source] at bound
  dsimp only [word] at bound
  exact ⟨_,by dsimp only [initialReadBudget,word];omega,
    moving.sequence (flag.sequence read)⟩

end Counting.StackMachine.NetworkVista.Run
