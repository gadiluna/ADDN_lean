import Counting.NetworkVistaRunState
import Counting.NetworkVistaRunRoundPrepare
import Counting.NetworkVistaReceiverStep
import Counting.DagRawLabels

namespace Counting.StackMachine.NetworkVista.Run
open Routine RealizabilityCall
set_option backward.isDefEq.respectTransparency false

def preparedData (input : Simulation.Input) (depth : Fin input.rounds.size) (counter : List Bool) : Fin 30→List Bool :=
  preparedRound (stateData input depth.val counter) input.rounds[depth.val]
    (Encoding.sequence matrixCodec (input.rounds.toList.drop (depth.val+1)))

theorem prepareRound_input_executes (input : Simulation.Input) (depth : Fin input.rounds.size) (counter : List Bool) :
    ∃ time ≤ prepareRoundBudget (stateData input depth.val counter),
      Executes prepareRound (file (stateData input depth.val counter)) time (file (preparedData input depth counter)) := by
  apply prepareRound_executes
  · change Encoding.sequence matrixCodec (input.rounds.toList.drop depth.val)=_
    rw [List.drop_eq_getElem_cons (by simp)]
    simp only [Encoding.sequence,Array.getElem_toList,matrixCodec]
  all_goals rfl

theorem preparedData_bounded (input : Simulation.Input) (depth : Fin input.rounds.size) (counter : List Bool)
    (count : counter.length ≤ input.rounds.size) :
    ∀ r,(preparedData input depth counter r).length ≤ stateCapacity input := by
  have old := stateData_bounded input depth.val counter (Nat.le_of_lt depth.isLt) count
  have remaining := remainingMatrices_length_bound input (depth.val+1)
  have graph : (matrixCodec.encode input.rounds[depth.val]).length ≤ (Encoding.networkInput.encode input).length := by
    have bound := Encoding.array_member_length_le matrixCodec input.rounds input.rounds[depth.val]
      (by simp only [Array.mem_toList_iff];exact Array.getElem_mem depth.isLt)
    have full : ((Encoding.array matrixCodec).encode input.rounds).length ≤
        (Encoding.networkInput.encode input).length := by rw [Encoding.networkInput_length];exact Nat.le_add_left _ _
    exact bound.trans full
  have n := Encoding.network_agents_le_length input
  have linear : (Encoding.networkInput.encode input).length+1 ≤
      ((Encoding.networkInput.encode input).length+1)^6 := Nat.le_self_pow (by decide) _
  intro r
  by_cases r3:r=3
  · subst r
    simp only [preparedData,preparedRound,Function.update_of_ne (by decide : (3:Fin 30)≠6),Function.update_self]
    change (matrixCodec.encode input.rounds[depth.val]).length ≤ stateCapacity input
    dsimp [stateCapacity];omega
  by_cases r6:r=6
  · subst r
    change (List.replicate input.leaders.size true).length ≤ stateCapacity input
    rw [List.length_replicate]
    dsimp [stateCapacity];omega
  by_cases r20:r=20
  · subst r
    simp only [preparedData,preparedRound,Function.update_of_ne (by decide : (20:Fin 30)≠6),
      Function.update_of_ne (by decide : (20:Fin 30)≠3),Function.update_self]
    dsimp [stateCapacity];omega
  simpa only [preparedData,preparedRound,Function.update_of_ne r6,Function.update_of_ne r3,
    Function.update_of_ne r20] using old r

theorem receiverUpdated_input (input : Simulation.Input) (depth : Fin input.rounds.size)
    (shape : Encoding.matrixShape input.leaders.size input.rounds[depth.val]=true)
    (receiver : Encoding.InputAgent input) :
    Receiver.receiverUpdated input.leaders.size depth.val (Encoding.inputLeader input)
      (Encoding.rawInputVistaRun input depth.val) input.rounds[depth.val] receiver=
        Encoding.rawInputVistaRun input (depth.val+1) receiver := by
  rw [Receiver.receiverUpdated_eq_rawUpdate _ _ _ _ _ _
    (fun agent=>(Encoding.rawInputVistaRun_correct input depth.val agent).1)
    (fun agent=>(Encoding.rawInputVistaRun_correct input depth.val agent).2.1)
    (Encoding.rawInputVistaRun_leader input depth.val)]
  rw [Encoding.rawInputVistaRun,Encoding.inputGraph_listed input depth]
  congr 1
  unfold Receiver.receiverDegree Receiver.receiverRow
  rw [Encoding.matrix_row_sum _ _ shape receiver,Encoding.finRange_sum]

end Counting.StackMachine.NetworkVista.Run
