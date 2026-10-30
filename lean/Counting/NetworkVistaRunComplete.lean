import Counting.NetworkVistaRunInitialState
import Counting.NetworkVistaRunLoopBase
import Counting.NetworkVistaRunOutput
import Counting.NetworkVistaRunRound

namespace Counting.StackMachine.NetworkVista.Run
open Routine RealizabilityCall
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 5000
set_option exponentiation.threshold 1024

private theorem roundsCost_bound (C L count time : Nat) (population : count ≤ L)
    (bound : time ≤ count*(C*(L+1)^372+2)+1) :
    time ≤ (C+3)*(L+1)^373 := by
  have scaled := Nat.mul_le_mul_right (C*(L+1)^372+2) (show count≤L+1 by omega)
  have linear : L+1≤(L+1)^373 := Nat.le_self_pow (by decide) _
  have one : 1≤(L+1)^373 := Nat.one_le_pow' _ _
  have powers : (L+1)*(C*(L+1)^372)=C*(L+1)^373 := by
    rw [pow_succ (L+1) 372]
    exact (Nat.mul_left_comm (L+1) C ((L+1)^372)).trans
      (congrArg (C*·) (Nat.mul_comm (L+1) ((L+1)^372)))
  simp only [Nat.mul_add] at scaled bound
  rw [powers] at scaled
  rw [Nat.add_mul]
  omega

private theorem completeCost_bound (C A N a b c : Nat) (positive : 1≤N)
    (first : a≤A*N^3) (middle : b≤(C+3)*N^373) (last : c≤141000*N^6) :
    a+1+(b+1+c) ≤ (C+A+141010)*N^373 := by
  have p3 : N^3≤N^373 := Nat.pow_le_pow_right positive (by decide)
  have p6 : N^6≤N^373 := Nat.pow_le_pow_right positive (by decide)
  have one : 1≤N^373 := one_le_pow₀ positive
  have f := first.trans (Nat.mul_le_mul_left A p3)
  have l := last.trans (Nat.mul_le_mul_left 141000 p6)
  rw [Nat.add_mul] at middle
  rw [Nat.add_mul,Nat.add_mul]
  omega

def allRounds : Routine 128 := forEach (context 21) oneRound

theorem allRounds_executes (input : Simulation.Input) (valid : Encoding.networkValid input=true) :
    ∃ time ≤ (oneRoundCoefficient+3)*((Encoding.networkInput.encode input).length+1)^373,
      Executes allRounds (file (stateData input 0 (List.replicate input.rounds.size true))) time
        (file (stateData input input.rounds.size [])) := by
  obtain ⟨time,bound,run⟩ := roundLoop_executes input oneRound
    (oneRoundCoefficient*((Encoding.networkInput.encode input).length+1)^372)
    (fun depth counter count=>oneRound_executes input depth counter count valid)
    0 (List.replicate input.rounds.size true) (by simp)
  simp only [List.length_replicate,Nat.zero_add] at bound run
  exact ⟨time,roundsCost_bound _ _ _ _ (Encoding.network_rounds_le_length input) bound,run⟩

def complete : Routine 128 := sequence setup (sequence allRounds finish)

def completeCoefficient : Nat := oneRoundCoefficient+setupCoefficient+141010

/-- The finite stack program reconstructs every observer's raw shared DAG,
uses an immutable previous configuration in each round, and erases all work. -/
theorem complete_executes (input : Simulation.Input) (valid : Encoding.networkValid input=true) :
    ∃ time ≤ completeCoefficient*((Encoding.networkInput.encode input).length+1)^373,
      Executes complete (inputStore 128 (Encoding.networkInput.encode input)) time
        (outputStore 128 ((Encoding.array Encoding.vista).encode (Encoding.rawInputVistas input))) := by
  obtain ⟨t0,b0,r0⟩ := setup_state_executes input
  obtain ⟨t1,b1,r1⟩ := allRounds_executes input valid
  obtain ⟨t2,b2,r2⟩ := finish_state_executes input
  refine ⟨_,?_,r0.sequence (r1.sequence r2)⟩
  exact completeCost_bound oneRoundCoefficient setupCoefficient _ _ _ _ (by omega) b0 b1 b2

end Counting.StackMachine.NetworkVista.Run
