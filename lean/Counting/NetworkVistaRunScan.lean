import Counting.NetworkVistaRunReceivers
import Counting.NetworkVistaRunRoundState

namespace Counting.StackMachine.NetworkVista.Run
open Routine RealizabilityCall
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
set_option maxRecDepth 200000

def scanRoles : Fin 4 ↪ Fin 130 := ⟨![106,104,105,107],by decide⟩
def scan : Routine 128 := receiverLoop 128 scanRoles Receiver.step

def scanData (data : Fin 30→List Bool) (counter index emitted : List Bool) : Fin 30→List Bool :=
  Function.update (Function.update (Function.update (Function.update data 6 counter) 4 index) 5 emitted) 7 []

theorem scanFrame_file (data : Fin 30→List Bool) (counter index emitted : List Bool) :
    receiverFrame scanRoles (file data) counter index emitted=file (scanData data counter index emitted) := by
  change Function.update (Function.update (Function.update (Function.update (file data)
    (context 6) counter) (context 4) index) (context 5) emitted) (context 7) []=_
  rw [file_update,file_update,file_update,file_update]
  rfl

def scanBound (input : Simulation.Input) : Nat :=
  Complexity.polynomial Receiver.stepCoefficient 61 (stateCapacity input)

def scannedData (input : Simulation.Input) (depth : Fin input.rounds.size) (counter : List Bool) : Fin 30→List Bool :=
  scanData (preparedData input depth counter) [] (List.replicate input.leaders.size true)
    (Encoding.sequence Encoding.vista (List.ofFn (Encoding.rawInputVistaRun input (depth.val+1)))).reverse

theorem scan_input_executes (input : Simulation.Input) (depth : Fin input.rounds.size)
    (counter : List Bool) (count : counter.length ≤ input.rounds.size)
    (shape : Encoding.matrixShape input.leaders.size input.rounds[depth.val]=true) :
    ∃ time ≤ input.leaders.size*(3*scanBound input+6)+1,
      Executes scan (file (preparedData input depth counter)) time (file (scannedData input depth counter)) := by
  let base := preparedData input depth counter
  let next := List.ofFn (Encoding.rawInputVistaRun input (depth.val+1))
  let capacity := stateCapacity input
  have baseBound := preparedData_bounded input depth counter count
  have positive : 1 ≤ capacity := by
    have one : 1 ≤ ((Encoding.networkInput.encode input).length+1)^6 := Nat.one_le_pow' _ _
    dsimp only [capacity,stateCapacity];omega
  have population : input.leaders.size ≤ capacity := by
    have bound := baseBound 6
    change (List.replicate input.leaders.size true).length ≤ capacity at bound
    simpa only [List.length_replicate] using bound
  have nextLength : (Encoding.sequence Encoding.vista next).length ≤ capacity := by
    have bound := viewArray_length_bound input (depth.val+1) (by have := depth.isLt;omega)
    rw [Encoding.rawInputVistaArrayRun_eq] at bound
    simp only [Encoding.array,Encoding.transport,Encoding.list,Array.toList_ofFn,List.length_ofFn,List.length_append] at bound
    change (Encoding.natural.encode input.leaders.size).length+(Encoding.sequence Encoding.vista next).length ≤ _ at bound
    dsimp only [capacity,stateCapacity]
    omega
  have each : ∀ (done : Nat) (vista : Executable.Vista),next[done]?=some vista →
      ∀ (remaining emitted : List Bool),remaining.length ≤ capacity → emitted.length ≤ capacity →
        ∃ time ≤ scanBound input,Executes Receiver.step
          (receiverFrame scanRoles (file base) remaining (List.replicate done true++[]) emitted) time
          (Function.update (receiverFrame scanRoles (file base) remaining (List.replicate done true++[]) emitted)
            (scanRoles 3) (Encoding.vista.encode vista)) := by
    intro done vista lookup remaining emitted remainingBound emittedBound
    have inside : done < input.leaders.size := by
      have member := (List.getElem?_eq_some_iff.mp lookup).1
      simpa only [next,List.length_ofFn] using member
    let receiver : Encoding.InputAgent input := ⟨done,inside⟩
    have viewEq : vista=Encoding.rawInputVistaRun input (depth.val+1) receiver := by
      have element := (List.getElem?_eq_some_iff.mp lookup).2
      simpa only [next,List.getElem_ofFn] using element.symm
    let data := scanData base remaining (List.replicate done true) emitted
    have leaderArray : Array.ofFn (Encoding.inputLeader input)=input.leaders := by
      exact Array.ext (by simp) (by intro i h₁ h₂;simp [Encoding.inputLeader])
    have bounded : ∀ r,(data r).length ≤ capacity := by
      intro r
      by_cases r4:r=4
      · subst r;simp only [data,scanData,Function.update_of_ne (by decide : (4:Fin 30)≠7),
          Function.update_of_ne (by decide : (4:Fin 30)≠5),Function.update_self,List.length_replicate]
        omega
      by_cases r5:r=5
      · subst r;simpa [data,scanData] using emittedBound
      by_cases r6:r=6
      · subst r;simpa [data,scanData] using remainingBound
      by_cases r7:r=7
      · subst r;simp [data,scanData]
      simpa only [data,scanData,Function.update_of_ne r4,Function.update_of_ne r5,
        Function.update_of_ne r6,Function.update_of_ne r7] using baseBound r
    obtain ⟨time,bound,run⟩ := Receiver.step_executes data input.leaders.size depth.val
      (Encoding.inputLeader input) (Encoding.rawInputVistaRun input depth.val) input.rounds[depth.val] receiver shape
      (by simp [data,scanData,base,preparedData,preparedRound,stateData])
      (by simp [data,scanData,base,preparedData,preparedRound,stateData,leaderArray])
      (by simp [data,scanData,base,preparedData,preparedRound,stateData,Encoding.rawInputVistaArrayRun_eq])
      (by simp [data,scanData,base,preparedData,preparedRound])
      (by simp [data,scanData,receiver]) (by
        intro r lo hi
        fin_cases r <;> simp_all [data,scanData,base,preparedData,preparedRound,stateData])
      capacity positive population bounded
    rw [receiverUpdated_input input depth shape receiver,←viewEq] at run
    refine ⟨time,bound,?_⟩
    simp only [List.append_nil,scanFrame_file]
    change Executes Receiver.step (file data) time
      (Function.update (file data) (context 7) (Encoding.vista.encode vista))
    rw [file_update]
    exact run
  have codeBound : ∀ vista∈next,(Encoding.vista.encode vista).length ≤ scanBound input := by
    intro vista member
    have length : (Encoding.vista.encode vista).length ≤ (Encoding.sequence Encoding.vista next).length := by
      rw [Encoding.sequence_length]
      exact List.single_le_sum (fun _ _=>Nat.zero_le _) _ (List.mem_map.mpr ⟨vista,member,rfl⟩)
    have power : capacity ≤ (capacity+1)^61 :=
      (Nat.le_succ _).trans (Nat.le_self_pow (by decide) _)
    have coefficient : 1 ≤ Receiver.stepCoefficient := by
      unfold Receiver.stepCoefficient
      omega
    have scale := Nat.mul_le_mul_right ((capacity+1)^61) coefficient
    change _ ≤ Receiver.stepCoefficient*(capacity+1)^61
    omega
  obtain ⟨time,bound,run⟩ := receiverLoop_bounded_executes 128 scanRoles Receiver.step (file base) next
    (List.replicate input.leaders.size true) [] [] (by simp [next]) (scanBound input) capacity
    (by simpa using population) (by simpa using nextLength) each codeBound
  rw [scanFrame_file,scanFrame_file] at run
  have initial : scanData base (List.replicate input.leaders.size true) [] []=base := by
    funext r
    fin_cases r <;> simp [scanData,base,preparedData,preparedRound,stateData]
  rw [initial] at run
  simp only [List.append_nil,List.length_ofFn,next] at run bound
  exact ⟨time,bound,run⟩

end Counting.StackMachine.NetworkVista.Run
