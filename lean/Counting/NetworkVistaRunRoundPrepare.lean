import Counting.StackNetworkCertificateRead
import Counting.NetworkRecognitionParser

namespace Counting.StackMachine.NetworkVista.Run
open Routine EncodingPrograms RealizabilityCall
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

def prepareRound : Routine 128 := sequence (pushBit (context 4) true)
  (sequence (NetworkCertificate.consumeField NetworkRecognition.matrix 20 3)
    (sequence (clearExternal 4) (copyExternal 22 6)))

def preparedRound (data : Fin 30→List Bool) (matrix : Simulation.RoundGraph) (suffix : List Bool) : Fin 30→List Bool :=
  Function.update (Function.update (Function.update data 20 suffix)
    3 ((Encoding.array (Encoding.array Encoding.natural)).encode matrix)) 6 (data 22)

def prepareRoundBudget (data : Fin 30→List Bool) : Nat :=
  Complexity.polynomial NetworkRecognition.matrix.coefficient NetworkRecognition.matrix.exponent (data 20).length+
    14*(data 20).length+5*(data 22).length+22

theorem prepareRound_executes (data : Fin 30→List Bool) (matrix : Simulation.RoundGraph)
    (suffix : List Bool)
    (source : data 20=(Encoding.array (Encoding.array Encoding.natural)).encode matrix++suffix)
    (e3 : data 3=[]) (e4 : data 4=[]) (e5 : data 5=[]) (e6 : data 6=[]) :
    ∃ time ≤ prepareRoundBudget data, Executes prepareRound (file data) time
      (file (preparedRound data matrix suffix)) := by
  have flag := pushBit_executes (context 4) true (file data)
  rw [file_context,e4,file_update] at flag
  let a := Function.update data 4 [true]
  obtain ⟨t,b,r⟩ := NetworkCertificate.consumeField_executes NetworkRecognition.matrix a 20 3
    (by decide) (by decide) (by decide) (by decide) (by decide) matrix suffix true []
    (by simp [a,source]) (by simp [a]) (by simp [a,e5]) (by simp [a,e3])
  let c := Function.update (Function.update a 20 suffix) 3
    ((Encoding.array (Encoding.array Encoding.natural)).encode matrix)
  have clear := clearExternal_executes c 4
  rw [show c 4=[true] by simp [c,a],List.length_singleton] at clear
  let d := Function.update c 4 []
  have count := copyExternal_executes d 22 6 (by decide)
  rw [show d 22=data 22 by simp [d,c,a],show d 6=[] by simp [d,c,a,e6],List.append_nil] at count
  have final : Function.update d 6 (data 22)=preparedRound data matrix suffix := by
    funext i
    fin_cases i <;> simp [preparedRound,d,c,a,e4]
  rw [final] at count
  refine ⟨_,?_,flag.sequence (r.sequence (clear.sequence count))⟩
  have a20 : a 20=data 20 := by simp [a]
  rw [a20] at b
  dsimp only [prepareRoundBudget]
  omega

end Counting.StackMachine.NetworkVista.Run
