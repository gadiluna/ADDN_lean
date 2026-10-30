import Counting.NetworkVistaRunScan
import Counting.NetworkVistaRunFinish

namespace Counting.StackMachine.NetworkVista.Run
open Routine RealizabilityCall
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
set_option maxRecDepth 5000
set_option exponentiation.threshold 1000

def oneRound : Routine 128 := sequence prepareRound (sequence scan finishRound)

def oneRoundCoefficient : Nat :=
  (3*Receiver.stepCoefficient+NetworkRecognition.matrix.coefficient+100)*1001^62

theorem scannedData_bounded (input : Simulation.Input) (depth : Fin input.rounds.size)
    (counter : List Bool) (count : counter.length ≤ input.rounds.size) :
    ∀ r,(scannedData input depth counter r).length ≤ stateCapacity input := by
  have old := preparedData_bounded input depth counter count
  have next := viewArray_length_bound input (depth.val+1) (by have := depth.isLt;omega)
  rw [Encoding.rawInputVistaArrayRun_eq] at next
  simp only [Encoding.array,Encoding.transport,Encoding.list,Array.toList_ofFn,
    List.length_ofFn,List.length_append] at next
  have n := Encoding.network_agents_le_length input
  have linear : (Encoding.networkInput.encode input).length+1 ≤
      ((Encoding.networkInput.encode input).length+1)^6 := Nat.le_self_pow (by decide) _
  intro r
  by_cases r4:r=4
  · subst r
    simp only [scannedData,scanData,Function.update_of_ne (by decide : (4:Fin 30)≠7),
      Function.update_of_ne (by decide : (4:Fin 30)≠5),Function.update_self,List.length_replicate]
    dsimp [stateCapacity];omega
  by_cases r5:r=5
  · subst r
    simp only [scannedData,scanData,Function.update_of_ne (by decide : (5:Fin 30)≠7),Function.update_self,List.length_reverse]
    dsimp [stateCapacity];omega
  by_cases r6:r=6
  · subst r;simp [scannedData,scanData]
  by_cases r7:r=7
  · subst r;simp [scannedData,scanData]
  simpa only [scannedData,scanData,Function.update_of_ne r4,Function.update_of_ne r5,
    Function.update_of_ne r6,Function.update_of_ne r7] using old r

private theorem round_budget_arithmetic (c p C X Y source population parserCost scanCost : Nat)
    (sourceBound : source ≤ C) (populationBound : population ≤ C) (successor : C+1=X)
    (linear : X≤Y) (_positive : 1≤Y) (parserBound : parserCost≤p*Y)
    (scanBounded : scanCost≤3*c*Y+6*X) :
    parserCost+14*source+5*population+22+(scanCost+1)+40*X+2≤(3*c+p+100)*Y := by
  rw [Nat.add_mul,Nat.add_mul,Nat.mul_assoc 3]
  rw [Nat.mul_assoc 3] at scanBounded
  omega

theorem oneRound_budget (input : Simulation.Input) (depth : Fin input.rounds.size)
    (counter : List Bool) (count : counter.length ≤ input.rounds.size) :
    prepareRoundBudget (stateData input depth.val counter)+
      (input.leaders.size*(3*scanBound input+6)+1)+40*(stateCapacity input+1)+2 ≤
      oneRoundCoefficient*((Encoding.networkInput.encode input).length+1)^372 := by
  let C := stateCapacity input
  let X := C+1
  have old := stateData_bounded input depth.val counter (Nat.le_of_lt depth.isLt) count
  have source : (stateData input depth.val counter 20).length ≤ C := old 20
  have population : input.leaders.size ≤ C := by
    have bound := old 22
    change (List.replicate input.leaders.size true).length ≤ C at bound
    simpa only [List.length_replicate] using bound
  have positive : 1 ≤ X := by dsimp [X];omega
  have linear : X ≤ X^62 := Nat.le_self_pow (by decide) _
  have one : 1 ≤ X^62 := one_le_pow₀ positive
  have parserDegree : NetworkRecognition.matrix.exponent ≤ 62 := by decide
  have parserPower := (Nat.pow_le_pow_left (show (stateData input depth.val counter 20).length+1 ≤ X by
    dsimp [X];omega) NetworkRecognition.matrix.exponent).trans
    (Nat.pow_le_pow_right positive parserDegree)
  have parserBound := Nat.mul_le_mul_left NetworkRecognition.matrix.coefficient parserPower
  have scanBounded := Nat.mul_le_mul_right (3*scanBound input+6) (show input.leaders.size ≤ X by dsimp [X];omega)
  have scanIdentity : X*(3*scanBound input+6)=3*Receiver.stepCoefficient*X^62+6*X := by
    change X*(3*(Receiver.stepCoefficient*X^61)+6)=3*Receiver.stepCoefficient*X^62+6*X
    rw [Nat.mul_add,←Nat.mul_assoc 3, Nat.mul_comm X (3*Receiver.stepCoefficient*X^61),
      Nat.mul_assoc (3*Receiver.stepCoefficient),←Nat.pow_succ,Nat.mul_comm X 6]
  rw [scanIdentity] at scanBounded
  have total : prepareRoundBudget (stateData input depth.val counter)+
      (input.leaders.size*(3*scanBound input+6)+1)+40*(stateCapacity input+1)+2 ≤
      (3*Receiver.stepCoefficient+NetworkRecognition.matrix.coefficient+100)*X^62 := by
    dsimp only [prepareRoundBudget,Complexity.polynomial]
    rw [show (stateData input depth.val counter 22).length=input.leaders.size by simp [stateData]]
    exact round_budget_arithmetic Receiver.stepCoefficient NetworkRecognition.matrix.coefficient
      C X (X^62) (stateData input depth.val counter 20).length input.leaders.size _ _
      source population rfl linear one parserBound scanBounded
  have cap : X ≤ 1001*((Encoding.networkInput.encode input).length+1)^6 := by
    have p : 1 ≤ ((Encoding.networkInput.encode input).length+1)^6 := Nat.one_le_pow' _ _
    dsimp only [X,C,stateCapacity]
    omega
  calc
    _ ≤ (3*Receiver.stepCoefficient+NetworkRecognition.matrix.coefficient+100)*X^62 := total
    _ ≤ (3*Receiver.stepCoefficient+NetworkRecognition.matrix.coefficient+100)*
      (1001*((Encoding.networkInput.encode input).length+1)^6)^62 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left cap 62)
    _ = _ := by
      change _=((3*Receiver.stepCoefficient+NetworkRecognition.matrix.coefficient+100)*1001^62)*
        ((Encoding.networkInput.encode input).length+1)^372
      rw [Nat.mul_pow,←Nat.pow_mul,←Nat.mul_assoc]

/-- One complete paid round reads the old configuration for all receivers,
then replaces it simultaneously and advances the actual encoded clock. -/
theorem oneRound_executes (input : Simulation.Input) (depth : Fin input.rounds.size)
    (counter : List Bool) (count : counter.length ≤ input.rounds.size)
    (valid : Encoding.networkValid input=true) :
    ∃ time ≤ oneRoundCoefficient*((Encoding.networkInput.encode input).length+1)^372,
      Executes oneRound (file (stateData input depth.val counter)) time
        (file (stateData input (depth.val+1) counter)) := by
  have shape := ((Encoding.networkValid_iff input).mp valid).2.2 depth |>.1
  obtain ⟨tp,bp,rp⟩ := prepareRound_input_executes input depth counter
  obtain ⟨ts,bs,rs⟩ := scan_input_executes input depth counter count shape
  let next := List.ofFn (Encoding.rawInputVistaRun input (depth.val+1))
  let after := scannedData input depth counter
  obtain ⟨tf,bf,rf⟩ := finishRound_executes after depth.val next
    (by simp [after,scannedData,scanData,preparedData,preparedRound,stateData])
    (by simp [after,scannedData,scanData,next])
    (by simp [after,scannedData,scanData,preparedData,preparedRound,stateData,next])
    (by simp [after,scannedData,scanData,preparedData,preparedRound,stateData])
    (by simp [after,scannedData,scanData,preparedData,preparedRound,stateData])
    (by simp [after,scannedData,scanData,preparedData,preparedRound,stateData])
    (stateCapacity input) (scannedData_bounded input depth counter count)
  have final : finishedRound after depth.val next=stateData input (depth.val+1) counter := by
    funext r
    fin_cases r <;> simp [finishedRound,after,scannedData,scanData,preparedData,preparedRound,stateData,next,
      Encoding.rawInputVistaArrayRun_eq,Encoding.array,Encoding.transport,matrixCodec]
  rw [final] at rf
  refine ⟨_,?_,rp.sequence (rs.sequence rf)⟩
  have total := oneRound_budget input depth counter count
  omega

end Counting.StackMachine.NetworkVista.Run
