import Counting.NetworkVistaRunTime
import Counting.EncodingNetwork

namespace Counting.StackMachine.NetworkVista.Run
open Routine EncodingPrograms RealizabilityCall
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

def finishRound : Routine 128 := sequence (clearExternal 2)
  (sequence (reverseExternal 5 2) (sequence (copyExternal 23 2)
    (sequence (clearExternal 4) (sequence incrementTime (clearExternal 3)))))

def finishedRound (data : Fin 30→List Bool) (round : Nat) (views : List Executable.Vista) : Fin 30→List Bool :=
  Function.update (Function.update (Function.update (Function.update (Function.update data
    2 ((Encoding.list Encoding.vista).encode views)) 5 []) 4 [])
    0 (Encoding.natural.encode (round+1))) 3 []

theorem finishRound_executes (data : Fin 30→List Bool) (round : Nat) (views : List Executable.Vista)
    (clock : data 0=Encoding.natural.encode round)
    (reversed : data 5=(Encoding.sequence Encoding.vista views).reverse)
    (header : data 23=Encoding.natural.encode views.length)
    (e24 : data 24=[]) (e25 : data 25=[]) (e26 : data 26=[])
    (bound : Nat) (bounded : ∀ r,(data r).length≤bound) :
    ∃ time ≤ 40*(bound+1), Executes finishRound (file data) time (file (finishedRound data round views)) := by
  have first := clearExternal_executes data 2
  let a := Function.update data 2 []
  have second := reverseExternal_executes a 5 2 (by decide)
  have a5 : a 5=data 5 := by simp [a]
  have a2 : a 2=[] := by simp [a]
  rw [a5,a2,reversed,List.reverse_reverse,List.append_nil,List.length_reverse] at second
  let b := Function.update (Function.update a 5 []) 2 (Encoding.sequence Encoding.vista views)
  have third := copyExternal_executes b 23 2 (by decide)
  have b23 : b 23=data 23 := by simp [b,a]
  have b2 : b 2=Encoding.sequence Encoding.vista views := by simp [b]
  rw [b23,b2,header] at third
  let c := Function.update b 2 ((Encoding.list Encoding.vista).encode views)
  have fourth := clearExternal_executes c 4
  have c4 : c 4=data 4 := by simp [c,b,a]
  rw [c4] at fourth
  let d := Function.update c 4 []
  obtain ⟨ti,bi,ri⟩ := incrementTime_executes d round
    (by simp [d,c,b,a,clock]) (by simp [d,c,b,a,e24])
    (by simp [d,c,b,a,e25]) (by simp [d,c,b,a,e26])
  let e := Function.update d 0 (Encoding.natural.encode (round+1))
  have last := clearExternal_executes e 3
  have e3 : e 3=data 3 := by simp [e,d,c,b,a]
  rw [e3] at last
  have final : Function.update e 3 []=finishedRound data round views := by
    funext r
    fin_cases r <;> simp [finishedRound,e,d,c,b,a]
  rw [final] at last
  refine ⟨_,?_,first.sequence (second.sequence (third.sequence (fourth.sequence (ri.sequence last))))⟩
  have b0 := bounded 0
  have b2 := bounded 2
  have b3 := bounded 3
  have b4 := bounded 4
  have b5 := bounded 5
  have b23 := bounded 23
  rw [reversed,List.length_reverse] at b5
  rw [header] at b23
  have d0 : d 0=data 0 := by simp [d,c,b,a]
  rw [d0] at bi
  omega

end Counting.StackMachine.NetworkVista.Run
