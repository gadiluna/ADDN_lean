import Counting.ExternalCoverValidationFacts
import Counting.ExternalCoverVerifierAccepted

namespace Counting.External.CoverVerification
open StackMachine StackMachine.Routine StackMachine.EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

def guardedVerifier (extra : Nat) (w : VerifierWorkspace extra) : Routine (extra+62) :=
  sequence (validationPrepare extra w)
    (branchRoutine (w 1) (acceptedVerifier extra w) (pushBit (w 1) false))

def guardedCoefficient := validationCoefficient+200020

theorem guardedVerifier_executes (extra : Nat) (w : VerifierWorkspace extra)
    (store : Fin (extra+64) → List Bool)
    (empty : ∀ i : Fin 64,i≠0 → i≠33 → store (w i)=[]) :
    ∃ time ≤ guardedCoefficient*((store (w 0)).length+(store (w 33)).length+1)^5,
      ∃ result,Executes (guardedVerifier extra w) store time result ∧
        result (w 1)=[checkEncodedMask (store (w 0)) (store (w 33))] := by
  obtain ⟨prepareTime,prepareBound,preparing⟩ := validationPrepare_executes extra w store empty
  let ready := validationPrepared extra w store
  let popped := Function.update ready (w 1) []
  let size := (store (w 0)).length+(store (w 33)).length+1
  have positive : 1 ≤ size^5 := Nat.one_le_pow _ _ (by dsimp [size];omega)
  by_cases valid : validationFlag extra w store=true
  · obtain ⟨input,encoded,sized⟩ := (validationFlag_iff extra w store).mp valid
    have canonical : ready=validationCanonical w store input := validationPrepared_canonical extra w store input encoded.symm
    have saved : popped (w 51)=X3CEncoding.codec.encode input := by
      simp [popped,canonical,validationCanonical,w.injective.eq_iff,encoded]
    have universeSize : popped (w 17)=List.replicate (3*input.1) true := by
      simp [popped,canonical,validationCanonical,w.injective.eq_iff]
    have count : popped (w 25)=List.replicate input.2.1 true := by
      simp [popped,canonical,validationCanonical,w.injective.eq_iff]
    have witness : popped (w 33)=store (w 33) := by
      simp [popped,canonical,validationCanonical,w.injective.eq_iff]
    have scratch (i : Fin 64) (n17 : i≠17) (n25 : i≠25) (n33 : i≠33) (n51 : i≠51) : popped (w i)=[] := by
      by_cases n1 : i=1
      · subst i;simp [popped]
      · by_cases n0 : i=0
        · subst i;simp [popped,canonical,validationCanonical,w.injective.eq_iff]
        · simp [popped,canonical,validationCanonical,w.injective.eq_iff,n0,n1,n17,n25,n51,empty i n0 n33]
    obtain ⟨verifyTime,verifyBound,result,verifying,output⟩ := acceptedVerifier_executes extra w input (store (w 33)) popped
      saved universeSize count witness sized scratch
    have branch := branch_executes_true (w 1) (acceptedVerifier extra w) (pushBit (w 1) false)
      ready result [] verifyTime (by simp [ready,validationPrepared,valid]) verifying
    refine ⟨prepareTime+1+(1+verifyTime),?_,result,preparing.sequence branch,?_⟩
    · have sourceSame : popped (w 51)=store (w 0) := saved.trans encoded
      rw [sourceSame] at verifyBound
      have verifyLimit : verifyTime ≤ 200010*size^5 :=
        verifyBound.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp [size];omega) _))
      change prepareTime ≤ validationCoefficient*size^5 at prepareBound
      change _ ≤ guardedCoefficient*size^5
      unfold guardedCoefficient
      nlinarith only [prepareBound,verifyLimit,positive]
    · rw [output]
      have decoded : X3CEncoding.codec.decodeExact (X3CEncoding.codec.encode input)=some input :=
        (X3CEncoding.codec.decodeExact_iff _ _).mpr rfl
      simp [checkEncodedMask,←encoded,decoded]
  · have invalid : validationFlag extra w store=false := Bool.eq_false_iff.mpr valid
    have pushing : Executes (pushBit (w 1) false) popped 1 (Function.update popped (w 1) [false]) := by
      simpa [popped] using pushBit_executes (w 1) false popped
    have branch := branch_executes_false (w 1) (acceptedVerifier extra w) (pushBit (w 1) false)
      ready _ [] 1 (by simp [ready,validationPrepared,invalid]) pushing
    have rejected : checkEncodedMask (store (w 0)) (store (w 33))=false := by
      apply Bool.eq_false_iff.mpr
      intro accepted
      exact valid (checkEncodedMask_implies_flag extra w store accepted)
    refine ⟨prepareTime+1+(1+1),?_,_,preparing.sequence branch,by simp [rejected]⟩
    change prepareTime ≤ validationCoefficient*size^5 at prepareBound
    change _ ≤ guardedCoefficient*size^5
    unfold guardedCoefficient
    nlinarith only [prepareBound,positive]

end Counting.External.CoverVerification
