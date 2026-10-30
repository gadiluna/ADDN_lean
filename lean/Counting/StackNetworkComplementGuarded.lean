import Counting.StackNetworkComplementTyped
import Counting.StackReadBranch

namespace Counting.StackMachine.NetworkComplement
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option exponentiation.threshold 1000
set_option maxHeartbeats 2200000

def answer (bit : Bool) : Routine 158 := pushBit (context 7) bit

theorem answer_executes (data : Fin 30→List Bool) (bit : Bool) (empty : data 7=[]) :
    Executes (answer bit) (file data) 1 (file (Function.update data 7 [bit])) := by
  have run := pushBit_executes (context 7) bit (file data)
  simpa only [answer,file_context,empty,file_update] using run

def networkGate : Routine 158 := branchRead (context 3) typed (answer true)
def networkGuarded : Routine 158 := sequence validate networkGate
def networkGuardedCoefficient := typedCoefficient+2000000000010

theorem networkGuarded_executes (data : Fin 30→List Bool)
    (empty : ∀r:Fin 30,r∈([3,4,5,6,7]:List (Fin 30)) → data r=[]) :
    ∃time≤Complexity.polynomial networkGuardedCoefficient 373 ((data 0).length+(data 1).length),
      ∃result, Executes networkGuarded (file data) time (file result) ∧
        result 7=[Counting.NetworkCertificate.binaryRawNetworkComplementVerifier (data 0) (data 1)] := by
  obtain ⟨t0,b0,r0⟩ := validate_executes data (empty 3 (by simp))
  let ready := Function.update data 3 [NetworkRecognition.validNetworkWord (data 0)]
  let N := (data 0).length+(data 1).length+1
  have positive : 1≤N := by dsimp [N];omega
  have power : ((data 0).length+1)^7≤N^373 :=
    (Nat.pow_le_pow_left (show (data 0).length+1≤N by dsimp [N];omega) 7).trans
      (Nat.pow_le_pow_right positive (by decide))
  have firstBound := b0.trans (Nat.mul_le_mul_left 2000000000000 power)
  have one : 1≤N^373 := Nat.one_le_pow _ _ positive
  cases decoded : Encoding.decodeNetwork? (data 0) with
  | none =>
    have flag : NetworkRecognition.validNetworkWord (data 0)=false := by
      rw [NetworkRecognition.validNetworkWord_eq_decodeNetwork,decoded];rfl
    have r1 := answer_executes ready true (by simp [ready,empty 7 (by simp)])
    have selected : Executes (if false then typed else answer true) (file ready) 1
        (file (Function.update ready 7 [true])) := r1
    have branched := branchRead_executes (context 3) typed (answer true) false []
      (file ready) (file (Function.update ready 7 [true])) 1 (by simp [ready,flag]) selected
    refine ⟨t0+1+(1+3),?_,Function.update ready 7 [true],r0.sequence branched,?_⟩
    · change _≤(typedCoefficient+2000000000010)*N^373
      rw [Nat.add_mul]
      omega
    · simp only [Function.update_self,Counting.NetworkCertificate.binaryRawNetworkComplementVerifier,decoded]
  | some input =>
    obtain ⟨encoded,valid⟩ := (Encoding.decodeNetwork_iff _ _).mp decoded
    have flag : NetworkRecognition.validNetworkWord (data 0)=true := by
      rw [NetworkRecognition.validNetworkWord_eq_decodeNetwork,decoded];rfl
    obtain ⟨t1,b1,r1⟩ := typed_executes ready input valid
      (by simpa [ready] using encoded.symm) (by
        intro r member
        have ne : r≠3 := by
          intro same
          subst r
          simp at member
        simpa [ready,ne] using empty r (by simpa only [List.mem_cons] using Or.inr member))
    have selected : Executes (if true then typed else answer true) (file ready) t1
        (file (typedData ready input)) := r1
    have branched := branchRead_executes (context 3) typed (answer true) true []
      (file ready) (file (typedData ready input)) t1 (by simp [ready,flag]) selected
    refine ⟨t0+1+(t1+3),?_,typedData ready input,r0.sequence branched,?_⟩
    · change t1≤typedCoefficient*N^373 at b1
      change _≤(typedCoefficient+2000000000010)*N^373
      rw [Nat.add_mul]
      omega
    · simp [typedData,ready]

def guarded : Routine 158 := branchRead (context 2) networkGuarded (answer false)
def guardedCoefficient := networkGuardedCoefficient+5

theorem guarded_executes (data : Fin 30→List Bool) (accepted : Bool)
    (flag : data 2=[accepted])
    (empty : ∀r:Fin 30,r∈([3,4,5,6,7]:List (Fin 30)) → data r=[]) :
    ∃time≤Complexity.polynomial guardedCoefficient 373 ((data 0).length+(data 1).length),
      ∃result, Executes guarded (file data) time (file result) ∧
        result 7=[accepted && Counting.NetworkCertificate.binaryRawNetworkComplementVerifier (data 0) (data 1)] := by
  have one : 1≤((data 0).length+(data 1).length+1)^373 := Nat.one_le_pow' _ _
  cases accepted
  · have r0 := answer_executes data false (empty 7 (by simp))
    have selected : Executes (if false then networkGuarded else answer false) (file data) 1
        (file (Function.update data 7 [false])) := r0
    have branched := branchRead_executes (context 2) networkGuarded (answer false) false []
      (file data) (file (Function.update data 7 [false])) 1 (by simp [flag]) selected
    refine ⟨4,?_,Function.update data 7 [false],branched,by simp⟩
    change _≤(networkGuardedCoefficient+5)*((data 0).length+(data 1).length+1)^373
    rw [Nat.add_mul]
    omega
  · obtain ⟨time,bound,result,run,output⟩ := networkGuarded_executes data empty
    have selected : Executes (if true then networkGuarded else answer false) (file data) time (file result) := run
    have branched := branchRead_executes (context 2) networkGuarded (answer false) true []
      (file data) (file result) time (by simp [flag]) selected
    refine ⟨time+3,?_,result,branched,by simpa only [Bool.true_and] using output⟩
    change time≤networkGuardedCoefficient*((data 0).length+(data 1).length+1)^373 at bound
    change _≤(networkGuardedCoefficient+5)*((data 0).length+(data 1).length+1)^373
    rw [Nat.add_mul]
    omega

end Counting.StackMachine.NetworkComplement
