import Counting.ExternalCoverVerifierRaw

namespace Counting.External.CoverVerification
open StackMachine StackMachine.Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def acceptedVerifier (extra : Nat) (w : VerifierWorkspace extra) : Routine (extra+62) :=
  sequence (pushBit (w 1) true)
    (sequence (ofProgram (ListPrograms.copyProgram (extra+61) (w 51) (w 0) (w 63))) (rawVerifier extra w))

theorem acceptedVerifier_executes (extra : Nat) (w : VerifierWorkspace extra)
    (input : X3CEncoding.Input) (mask : List Bool) (store : Fin (extra+64) → List Bool)
    (saved : store (w 51)=X3CEncoding.codec.encode input)
    (universeSize : store (w 17)=List.replicate (3*input.1) true)
    (count : store (w 25)=List.replicate input.2.1 true) (witness : store (w 33)=mask)
    (sized : mask.length=input.2.1)
    (empty : ∀ i : Fin 64,i≠17 → i≠25 → i≠33 → i≠51 → store (w i)=[]) :
    ∃ time ≤ 200010*((store (w 51)).length+1)^5,
      ∃ result,Executes (acceptedVerifier extra w) store time result ∧ result (w 1)=[checkMask input mask] := by
  let initialized := Function.update store (w 1) [true]
  have initializing : Executes (pushBit (w 1) true) store 1 initialized := by
    simpa [initialized,empty] using pushBit_executes (w 1) true store
  have copying := copy_executes (extra+61) (w 51) (w 0) (w 63)
    (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) initialized
    (by simp [initialized,w.injective.eq_iff,empty])
  have savedAt : initialized (w 51)=store (w 51) := by simp [initialized,w.injective.eq_iff]
  have sourceAt : initialized (w 0)=[] := by simp [initialized,w.injective.eq_iff,empty]
  rw [savedAt,sourceAt,List.append_nil] at copying
  let ready := Function.update initialized (w 0) (store (w 51))
  have readyEmpty (i : Fin 64) (n0 : i≠0) (n1 : i≠1) (n17 : i≠17) (n25 : i≠25) (n33 : i≠33) (n51 : i≠51) :
      ready (w i)=[] := by simp [ready,initialized,w.injective.eq_iff,n0,n1,empty i n17 n25 n33 n51]
  obtain ⟨verifyTime,verifyBound,result,verifying,output⟩ := rawVerifier_executes extra w input mask ready true []
    (by simp [ready,saved]) (by simp [ready,initialized,w.injective.eq_iff])
    (by simp [ready,initialized,w.injective.eq_iff,universeSize])
    (by simp [ready,initialized,w.injective.eq_iff,count])
    (by simp [ready,initialized,w.injective.eq_iff,witness]) sized readyEmpty
  simp only [ready,Function.update_self] at verifyBound
  refine ⟨1+1+(5*(store (w 51)).length+2+1+verifyTime),?_,result,
    initializing.sequence (copying.sequence verifying),by simpa using output⟩
  have linear : (store (w 51)).length+1 ≤ ((store (w 51)).length+1)^5 := Nat.le_self_pow (by decide) _
  omega

end Counting.External.CoverVerification
