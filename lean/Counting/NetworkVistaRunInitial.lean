import Counting.NetworkVistaRunInitialRead
import Counting.NetworkVistaRunInitialViews
import Counting.NetworkVistaRunInitialHeader

namespace Counting.StackMachine.NetworkVista.Run
open Routine EncodingPrograms RealizabilityCall
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-- Initialize every persistent register from the actual binary network input.
The matrix tape contains the sequence after its length prefix has been read. -/
def setup : Routine 128 := sequence initialRead (sequence initializeViews
  (sequence initialRoundHeader (sequence initialPopulation
    (sequence (pushBit (context 0) false)
      (sequence (clearExternal 4) (clearExternal 15))))))

def setupData (input : Simulation.Input) : Fin 30→List Bool :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (fun _=>[]) 0 (Encoding.natural.encode 0))
      1 ((Encoding.array Encoding.boolean).encode input.leaders))
      2 ((Encoding.array Encoding.vista).encode (input.leaders.map Executable.initialVista)))
      20 (Encoding.sequence (Encoding.array (Encoding.array Encoding.natural)) input.rounds.toList))
      21 (List.replicate input.rounds.size true))
      22 (List.replicate input.leaders.size true))
      23 (Encoding.natural.encode input.leaders.size)

def setupCoefficient : Nat := NetworkRecognition.booleans.coefficient+5000

/-- No validity hypothesis is needed for initialization: every typed network
input, including empty or malformed matrix arrays, is parsed faithfully. -/
theorem setup_executes (input : Simulation.Input) :
    ∃ time ≤ setupCoefficient*((Encoding.networkInput.encode input).length+1)^3,
      Executes setup (inputStore 128 (Encoding.networkInput.encode input)) time (file (setupData input)) := by
  obtain ⟨tr,br,rr⟩ := initialRead_executes input
  let a := initialReadData input
  obtain ⟨tv,bv,rv⟩ := initializeViews_executes a input.leaders
    (by simp [a,initialReadData]) (by simp [a,initialReadData])
    (by simp [a,initialReadData]) (by simp [a,initialReadData]) (by simp [a,initialReadData])
  let b := initializedViews a input.leaders
  obtain ⟨th,bh,rh⟩ := initialRoundHeader_executes b input.rounds
    (by simp [b,initializedViews,a,initialReadData])
    (by simp [b,initializedViews,a,initialReadData])
    (by simp [b,initializedViews,a,initialReadData])
  let c := initialRoundData b input.rounds
  obtain ⟨tn,bn,rn⟩ := initialPopulation_executes c
    (by simp [c,initialRoundData,b,initializedViews,a,initialReadData])
  let d := Function.update c 23 (Encoding.natural.encode (c 22).length)
  have push := pushBit_executes (context 0) false (file d)
  rw [file_context,show d 0=[] by simp [d,c,initialRoundData,b,initializedViews,a,initialReadData],file_update] at push
  let e := Function.update d 0 [false]
  have firstClear := clearExternal_executes e 4
  rw [show e 4=[true] by simp [e,d,c,initialRoundData,b,initializedViews,a,initialReadData],List.length_singleton] at firstClear
  let f := Function.update e 4 []
  have lastClear := clearExternal_executes f 15
  rw [show f 15=[true] by simp [f,e,d,c,initialRoundData,b,initializedViews],List.length_singleton] at lastClear
  have final : Function.update f 15 []=setupData input := by
    funext r
    fin_cases r <;> simp [f,e,d,c,initialRoundData,b,initializedViews,a,initialReadData,setupData,Encoding.natural,Encoding.frame]
  rw [final] at lastClear
  refine ⟨_,?_,rr.sequence (rv.sequence (rh.sequence (rn.sequence (push.sequence (firstClear.sequence lastClear)))))⟩
  have a1 : a 1=(Encoding.array Encoding.boolean).encode input.leaders := by simp [a,initialReadData]
  have b20 : b 20=(Encoding.array (Encoding.array (Encoding.array Encoding.natural))).encode input.rounds := by
    simp [b,initializedViews,a,initialReadData]
  have c22 : (c 22).length=input.leaders.size := by simp [c,initialRoundData,b,initializedViews]
  rw [a1] at bv
  rw [b20] at bh
  rw [c22] at bn
  let L := (Encoding.networkInput.encode input).length
  have leadersBound : ((Encoding.array Encoding.boolean).encode input.leaders).length≤L := by
    dsimp only [L];rw [Encoding.networkInput_length];omega
  have roundsBound : ((Encoding.array (Encoding.array (Encoding.array Encoding.natural))).encode input.rounds).length≤L := by
    dsimp only [L];rw [Encoding.networkInput_length];omega
  have nBound : input.leaders.size≤L := Encoding.network_agents_le_length input
  have p2 : (L+1)^2≤(L+1)^3 := Nat.pow_le_pow_right (by omega) (by decide)
  have p1 : L+1≤(L+1)^3 := Nat.le_self_pow (by decide) _
  have viewsBound : tv≤2010*(L+1)^3 := bv.trans (by gcongr)
  have headerBound : th≤1820*(L+1)^3 := bh.trans (by gcongr)
  have populationBound : tn≤20*(L+1)^3 := bn.trans (by calc
    20*(input.leaders.size+1)^2≤20*(L+1)^2 := by gcongr
    _≤20*(L+1)^3 := Nat.mul_le_mul_left _ p2)
  change tr≤NetworkRecognition.booleans.coefficient*(L+1)^3+20*L+20 at br
  change _ ≤ setupCoefficient*(L+1)^3
  dsimp only [setupCoefficient]
  nlinarith

end Counting.StackMachine.NetworkVista.Run
