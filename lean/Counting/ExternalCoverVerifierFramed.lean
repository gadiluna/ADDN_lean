import Counting.ExternalCoverVerifierGuard

namespace Counting.External.CoverVerification
open StackMachine StackMachine.Routine StackMachine.EncodingPrograms
set_option backward.isDefEq.respectTransparency false

def framedGuard (extra : Nat) (w : VerifierWorkspace extra) : Routine (extra+62) :=
  branchRoutine (w 1) (guardedVerifier extra w) (pushBit (w 1) false)

theorem framedGuard_executes (extra : Nat) (w : VerifierWorkspace extra)
    (store : Fin (extra+64) → List Bool) (flag : Bool) (status : store (w 1)=[flag])
    (empty : ∀ i : Fin 64,i≠0 → i≠1 → i≠33 → store (w i)=[]) :
    ∃ time ≤ (guardedCoefficient+2)*((store (w 0)).length+(store (w 33)).length+1)^5,
      ∃ result,Executes (framedGuard extra w) store time result ∧
        result (w 1)=[flag && checkEncodedMask (store (w 0)) (store (w 33))] := by
  let popped := Function.update store (w 1) []
  have source : popped (w 0)=store (w 0) := by simp [popped,w.injective.eq_iff]
  have witness : popped (w 33)=store (w 33) := by simp [popped,w.injective.eq_iff]
  have positive : 1 ≤ ((store (w 0)).length+(store (w 33)).length+1)^5 := Nat.one_le_pow _ _ (by omega)
  cases flag with
  | false =>
    have pushing : Executes (pushBit (w 1) false) popped 1 (Function.update popped (w 1) [false]) := by
      simpa [popped] using pushBit_executes (w 1) false popped
    refine ⟨2,?_,_,branch_executes_false (w 1) (guardedVerifier extra w) (pushBit (w 1) false)
      store _ [] 1 status pushing,by simp⟩
    nlinarith
  | true =>
    have cleared (i : Fin 64) (n0 : i≠0) (n33 : i≠33) : popped (w i)=[] := by
      by_cases n1 : i=1
      · subst i;simp [popped]
      · simp [popped,w.injective.eq_iff,n1,empty i n0 n1 n33]
    obtain ⟨time,bound,result,execution,output⟩ := guardedVerifier_executes extra w popped cleared
    rw [source,witness] at bound output
    refine ⟨1+time,by nlinarith,result,
      branch_executes_true (w 1) (guardedVerifier extra w) (pushBit (w 1) false) store result [] time status execution,?_⟩
    simpa using output

end Counting.External.CoverVerification
