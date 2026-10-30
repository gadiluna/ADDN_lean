import Counting.DagRawPhysical
import Counting.StackRealizabilityCallFile

namespace Counting.StackMachine.NetworkVista.Run
open Routine EncodingPrograms RealizabilityCall

def matrixCodec := Encoding.array (Encoding.array Encoding.natural)

def stateData (input : Simulation.Input) (depth : Nat) (counter : List Bool) : Fin 30→List Bool :=
  fun r=>match r.val with
  | 0 => Encoding.natural.encode depth
  | 1 => (Encoding.array Encoding.boolean).encode input.leaders
  | 2 => (Encoding.array Encoding.vista).encode (Encoding.rawInputVistaArrayRun input depth)
  | 20 => Encoding.sequence matrixCodec (input.rounds.toList.drop depth)
  | 21 => counter
  | 22 => List.replicate input.leaders.size true
  | 23 => Encoding.natural.encode input.leaders.size
  | _ => []

theorem viewArray_length_bound (input : Simulation.Input) (depth : Nat)
    (within : depth ≤ input.rounds.size) :
    ((Encoding.array Encoding.vista).encode (Encoding.rawInputVistaArrayRun input depth)).length ≤ 
      203*((Encoding.networkInput.encode input).length+1)^6 := by
  let L := (Encoding.networkInput.encode input).length
  have count := Encoding.network_agents_le_length input
  have header : input.leaders.size.size ≤ input.leaders.size := Nat.size_le.mpr Nat.lt_two_pow_self
  have entries : ((Encoding.rawInputVistaArrayRun input depth).toList.map
      (fun view=>(Encoding.vista.encode view).length)).sum ≤ input.leaders.size*(200*(L+1)^5) := by
    rw [Encoding.rawInputVistaArrayRun_eq,Array.toList_ofFn]
    have bound := List.sum_le_sum (l:=List.ofFn (Encoding.rawInputVistaRun input depth))
      (f:=fun view=>(Encoding.vista.encode view).length) (g:=fun _=>200*(L+1)^5) (by
        intro view member
        obtain ⟨i,rfl⟩ := List.mem_ofFn.mp member
        exact Encoding.rawInputVistaRun_encoding_length input depth within i)
    simpa only [List.map_const',List.sum_replicate,List.length_ofFn,smul_eq_mul] using bound
  rw [Encoding.array_length,Encoding.rawInputVistaArrayRun_eq,Array.size_ofFn]
  rw [Encoding.rawInputVistaArrayRun_eq] at entries
  have scale := Nat.mul_le_mul_right (200*(L+1)^5) (show input.leaders.size ≤ L+1 by omega)
  have linear : L+1 ≤ (L+1)^6 := Nat.le_self_pow (by decide) _
  change _  ≤  203*(L+1)^6
  nlinarith only [entries,scale,header,count,linear,show (L+1)*(200*(L+1)^5)=200*(L+1)^6 by ring]

theorem remainingMatrices_length_bound (input : Simulation.Input) (depth : Nat) :
    (Encoding.sequence matrixCodec (input.rounds.toList.drop depth)).length ≤ 
      (Encoding.networkInput.encode input).length := by
  have split := List.take_append_drop depth input.rounds.toList
  have length : (Encoding.sequence matrixCodec input.rounds.toList).length=
      (Encoding.sequence matrixCodec (input.rounds.toList.take depth)).length+
      (Encoding.sequence matrixCodec (input.rounds.toList.drop depth)).length := by
    conv_lhs => arg 1;arg 2;rw [←split]
    simp only [Encoding.sequence_length,List.map_append,List.sum_append]
  have whole : (Encoding.sequence matrixCodec input.rounds.toList).length ≤ 
      (Encoding.networkInput.encode input).length := by
    rw [Encoding.networkInput_length]
    simp only [Encoding.array,Encoding.transport,Encoding.list,List.length_append,matrixCodec]
    omega
  omega

def stateCapacity (input : Simulation.Input) : Nat :=
  1000*((Encoding.networkInput.encode input).length+1)^6

theorem stateData_bounded (input : Simulation.Input) (depth : Nat) (counter : List Bool)
    (within : depth ≤ input.rounds.size) (count : counter.length ≤ input.rounds.size) :
    ∀ r,(stateData input depth counter r).length ≤ stateCapacity input := by
  have views := viewArray_length_bound input depth within
  have remaining := remainingMatrices_length_bound input depth
  have agents := Encoding.network_agents_le_length input
  have rounds := Encoding.network_rounds_le_length input
  have dep : depth.size ≤ depth := Nat.size_le.mpr Nat.lt_two_pow_self
  have pop : input.leaders.size.size ≤ input.leaders.size := Nat.size_le.mpr Nat.lt_two_pow_self
  have leaders : ((Encoding.array Encoding.boolean).encode input.leaders).length ≤ 
      (Encoding.networkInput.encode input).length := by rw [Encoding.networkInput_length];omega
  have linear : (Encoding.networkInput.encode input).length+1 ≤ 
      ((Encoding.networkInput.encode input).length+1)^6 := Nat.le_self_pow (by decide) _
  intro r
  fin_cases r <;> simp only [stateData,Encoding.natural_length,List.length_replicate,List.length_nil]
  all_goals dsimp only [stateCapacity];omega

end Counting.StackMachine.NetworkVista.Run
