import Counting.MachineCountingRuntimeSemantics
import Counting.MachineCountingRuntimeAccumulation
import Counting.MachineProtocolAdvance
import Counting.MachineProtocolInitialize

namespace Counting.Machine.CountingRuntime
open Executable StackMachine.ProtocolAdvance
open scoped BigOperators
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000

/-- Actual finite-tape executions for initialization and every live local
round. Their outputs are the states of the already verified distributed run;
the cost is the sum of physical transition counts, including initialization. -/
def LocalRuntimeBound {V : Type} [Fintype V] (core : Bool)
    (G : Nat → V → V → Nat) (leader : V → Bool) (ell : Nat) (observer : V) (bound : Nat) : Prop :=
  ∃ (initialTime : Nat) (initialOutput : Config initializeStateProgram)
    (times : Fin (stoppingTime core (Fintype.card V) ell) → Nat)
    (outputs : Fin (stoppingTime core (Fintype.card V) ell) → Config (advanceProgram core)),
    initialTime+(∑ round,times round) ≤ bound ∧
    HaltsAt initializeStateProgram (StackMachine.ProtocolInitialize.inputWord ell (leader observer)) initialTime initialOutput ∧
    initialOutput.tape.denotes=Turing.Tape.mk₁
      ((stateWord (initialState ell (leader observer))).map bitSymbol) ∧
    ∀ round,
      HaltsAt (advanceProgram core) (roundInput core G leader ell round.val observer) (times round) (outputs round) ∧
      (outputs round).tape.denotes=Turing.Tape.mk₁
        ((outputWord (some (runState core G leader ell (round.val+1) observer))).map bitSymbol)

theorem LocalRuntimeBound.mono {V : Type} [Fintype V] {core : Bool}
    {G : Nat → V → V → Nat} {leader : V → Bool} {ell : Nat} {observer : V} {first last : Nat}
    (run : LocalRuntimeBound core G leader ell observer first) (bound : first ≤ last) :
    LocalRuntimeBound core G leader ell observer last := by
  obtain ⟨initialTime,initialOutput,times,outputs,cost,initial,initialTape,rounds⟩ := run
  exact ⟨initialTime,initialOutput,times,outputs,cost.trans bound,initial,initialTape,rounds⟩

/-- Both the original core algorithm and its exact-round optimization have
polynomial total local computation in population and binary arc-label size.
The programs, coefficient and degree are fixed before the network is chosen. -/
theorem local_runtime_polynomial (core : Bool) : ∃ coefficient degree,
    ∀ {V : Type} [Fintype V] (G : Nat → V → V → Nat) (leader : V → Bool) (ell M : Nat),
      Counting.Admissible ell G leader →
      (∀ r,0 < r → r ≤ 2*Fintype.card V → arcMass G r ≤ M) →
      ∀ observer,LocalRuntimeBound core G leader ell observer
        (coefficient*(Fintype.card V+M.size+1)^degree) := by
  classical
  obtain ⟨C,d,advance⟩ := advance_polynomial core
  let A := C*4000^d
  let I := 20*106^2*9
  refine ⟨2*A+I,6*d+3,?_⟩
  intro V inst G leader ell M network mass observer
  let N := Fintype.card V+M.size+1
  let stop := stoppingTime core (Fintype.card V) ell
  have positive : 1 ≤ N := by dsimp [N];omega
  have each (round : Fin stop) : ∃ (time : Nat) (output : Config (advanceProgram core)),
      time ≤ A*N^(6*d) ∧
      HaltsAt (advanceProgram core) (roundInput core G leader ell round.val observer) time output ∧
      output.tape.denotes=Turing.Tape.mk₁
        ((outputWord (some (runState core G leader ell (round.val+1) observer))).map bitSymbol) := by
    have previous := runState_before core G leader ell network round.val round.isLt observer
    obtain ⟨time,output,cost,halted,tape⟩ := advance
      (runState core G leader ell round.val observer) (messagesAt core G leader ell round.val observer)
      (∑ sender,G (round.val+1) observer sender) previous.1.valid
      (live_messages_valid core G leader ell network round.val round.isLt observer)
    have inputBound := live_input_bound core G leader ell M network round.val round.isLt mass observer
    have substituted := input_polynomial_substitution (roundInput core G leader ell round.val observer).length
      C d (Fintype.card V) M.size inputBound
    have next : transition core (runState core G leader ell round.val observer)
        (messagesAt core G leader ell round.val observer) (∑ sender,G (round.val+1) observer sender)=
          some (runState core G leader ell (round.val+1) observer) :=
      runState_next core G leader ell network round.val observer
    rw [next] at tape
    exact ⟨time,output,cost.trans substituted,halted,tape⟩
  choose times outputs costs halts tapes using each
  obtain ⟨initialTime,initialOutput,initialCost,initialHalt,initialTape⟩ :=
    initializeState_population_bound ell (Fintype.card V) (leader observer) network.leaderCount_le_card
  have summed := Finset.sum_le_sum (s:=Finset.univ)
    (f:=times) (g:=fun _=>A*N^(6*d)) (fun round _=>costs round)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at summed
  have count : stop ≤ 2*N := by
    have bound := stoppingTime_le_twice core (Fintype.card V) ell
    dsimp [stop,N];omega
  have multiplied := Nat.mul_le_mul_right (A*N^(6*d)) count
  have product : (2*N)*(A*N^(6*d))=2*A*N^(6*d+1) := by rw [pow_succ];ring
  rw [product] at multiplied
  have sumBound := summed.trans multiplied
  have lower : (Fintype.card V+1)^2 ≤ N^2 := Nat.pow_le_pow_left (by dsimp [N];omega) 2
  have p2 : N^2 ≤ N^(6*d+3) := Nat.pow_le_pow_right positive (by omega)
  have pr : N^(6*d+1) ≤ N^(6*d+3) := Nat.pow_le_pow_right positive (by omega)
  have initialBound : initialTime ≤ I*N^(6*d+3) := initialCost.trans
    (Nat.mul_le_mul_left I (lower.trans p2))
  have roundsBound : (∑ round,times round) ≤ 2*A*N^(6*d+3) := sumBound.trans
    (Nat.mul_le_mul_left (2*A) pr)
  refine ⟨initialTime,initialOutput,times,outputs,?_,initialHalt,initialTape,?_⟩
  · change initialTime+(∑ round,times round) ≤ (2*A+I)*N^(6*d+3)
    rw [Nat.add_mul]
    omega
  · exact fun round=>⟨halts round,tapes round⟩

/-- The formal runtime clauses of both Counting theorems, under the paper's
at-most-exponentially-many-arcs assumption, with every local phase charged. -/
theorem local_runtime_under_polynomial_arc_bound (core : Bool) (arcCoefficient arcExponent : Nat) :
    ∃ coefficient degree,
      ∀ {V : Type} [Fintype V] (G : Nat → V → V → Nat) (leader : V → Bool) (ell : Nat),
        Counting.Admissible ell G leader →
        (∀ r,0 < r → r ≤ 2*Fintype.card V →
          arcMass G r ≤ 2^(arcCoefficient*Fintype.card V^arcExponent)) →
        ∀ observer,LocalRuntimeBound core G leader ell observer (coefficient*(Fintype.card V+1)^degree) := by
  obtain ⟨C,d,run⟩ := local_runtime_polynomial core
  refine ⟨C*(arcCoefficient+3)^d,(arcExponent+1)*d,?_⟩
  intro V inst G leader ell network mass observer
  have actual := run G leader ell (2^(arcCoefficient*Fintype.card V^arcExponent)) network mass observer
  apply actual.mono
  have substituted := Nat.mul_le_mul_left C
    (arc_power_substitution (Fintype.card V) arcCoefficient arcExponent d)
  simpa only [Nat.mul_assoc] using substituted

end Counting.Machine.CountingRuntime
