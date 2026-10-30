import Counting.StackRealizabilityRoundItem

namespace Counting.StackMachine.RealizabilityCheck
open Routine RealizabilityVerifier
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
set_option maxRecDepth 8000

def roundOuterData (counter : List Bool) (auxiliary : Fin 2→List Bool) : Fin 3→List Bool :=
  ![counter,auxiliary 0,auxiliary 1]

def roundScan : Routine 98 := forEach 97 roundItem

theorem roundScan_counter (nodes : List Executable.Node) (values : List Nat) (N r : Nat)
    (status counter next : List Bool) (auxiliary : Fin 2→List Bool) :
    Function.update (roundFile (roundInputData nodes values N r status (roundOuterData counter auxiliary)))
      97 next=roundFile (roundInputData nodes values N r status (roundOuterData next auxiliary)) := by
  change Function.update (roundFile _) (roundContext 17) next=_
  rw [roundFile_update]
  congr 1
  funext i
  fin_cases i <;> simp [roundInputData,roundOuterData]

theorem roundScan_executes (vista : Executable.Vista) (weights : Array Nat)
    (valid : vista.valid=true) (length : weights.size=vista.nodes.size)
    (N : Nat) (tail : List Bool) (auxiliary : Fin 2→List Bool) (bits : List Bool) (r : Nat) (accepted : Bool) :
    let S := massInputSize vista.nodes.toList weights.toList+N.size+vista.nodes.size+r+bits.length+4
    ∃ time ≤ bits.length*(2000000000000000000000000*S^24+2)+1,
      Executes roundScan
        (roundFile (roundInputData vista.nodes.toList weights.toList N r (accepted::tail)
          (roundOuterData bits auxiliary))) time
        (roundFile (roundInputData vista.nodes.toList weights.toList N (r+bits.length)
          ((accepted && (List.range' r bits.length).all (checkedRound vista weights N))::tail)
          (roundOuterData [] auxiliary))) := by
  dsimp only
  induction bits generalizing r accepted with
  | nil =>
    obtain ⟨ran,halted⟩ := repeat_empty (97:Fin 100) roundItem
      (roundFile (roundInputData vista.nodes.toList weights.toList N r (accepted::tail)
        (roundOuterData [] auxiliary))) (by simp [roundFile,roundInputData,roundOuterData])
    exact ⟨1,by simp,⟨1,_⟩,ran,halted,by simp⟩
  | cons bit bits ih =>
    let nextAccepted := accepted && checkedRound vista weights N r
    obtain ⟨bodyTime,bodyBound,bodyFinish,bodyRun,bodyHalted,bodyStore⟩ :=
      roundItem_executes vista weights valid length N r accepted tail (roundOuterData bits auxiliary)
    obtain ⟨tailTime,tailBound,tailFinish,tailRun,tailHalted,tailStore⟩ := ih (r+1) nextAccepted
    let original := roundFile (roundInputData vista.nodes.toList weights.toList N r (accepted::tail)
      (roundOuterData (bit::bits) auxiliary))
    have iteration := repeat_iteration (97:Fin 100) roundItem original bit bits
      (by simp [original,roundFile,roundInputData,roundOuterData]) bodyTime bodyFinish
      (by simpa only [original,roundScan_counter] using bodyRun) bodyHalted
    refine ⟨bodyTime+2+tailTime,?_,tailFinish,?_,tailHalted,?_⟩
    · let S := massInputSize vista.nodes.toList weights.toList+N.size+vista.nodes.size+r+(bit::bits).length+4
      have rSize : r.size ≤ r := Nat.size_le.mpr Nat.lt_two_pow_self
      have bodySmall : roundSize vista.nodes.toList weights.toList N r ≤ S := by
        dsimp only [roundSize,S]
        simp only [Array.length_toList,List.length_cons]
        omega
      have bodyLimit := bodyBound.trans (Nat.mul_le_mul_left 2000000000000000000000000
        (Nat.pow_le_pow_left bodySmall 24))
      have tailSize : massInputSize vista.nodes.toList weights.toList+N.size+vista.nodes.size+(r+1)+bits.length+4=S := by
        dsimp only [S];simp only [List.length_cons];omega
      rw [tailSize] at tailBound
      change bodyTime+2+tailTime ≤ (bit::bits).length*(2000000000000000000000000*S^24+2)+1
      simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
    · change Machine.run (step roundScan.program) (bodyTime+2) ⟨0,original⟩=some ⟨0,bodyFinish.store⟩ at iteration
      rw [Machine.run_add,iteration,Option.bind_some,bodyStore]
      exact tailRun
    · apply tailStore.trans
      congr 2
      · simp only [List.length_cons];omega
      · simp [nextAccepted,List.range'_succ,Bool.and_assoc]

end Counting.StackMachine.RealizabilityCheck
