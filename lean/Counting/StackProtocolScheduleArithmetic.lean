import Counting.StackRoutineFixedPrefix
import Counting.StackEncodingBranch
import Counting.StackDagIncrement

namespace Counting.StackMachine.ProtocolSchedule
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

/-- One physical bit pop computes floor division by two on the canonical
little-endian payload, including zero. -/
theorem halve_executes (target : Fin (extra+2)) (store : Store extra) (n : Nat)
    (source:store target=n.bits) :
    Executes (discardBit target) store 1 (Function.update store target (n/2).bits) := by
  have run:=discardBit_executes target store
  rw [source,←Nat.div2_bits_eq_tail,Nat.div2_val] at run
  exact run

abbrev splitRound (source output : Fin (extra+2)) : Routine extra :=
  branchRoutine source (pushBit output true) (pushBit output false)

theorem splitRound_word_executes (source output : Fin (extra+2)) (different:source≠output)
    (store : Store extra) :
    Executes (splitRound source output) store 2
      (Function.update (Function.update store source (store source).tail) output
        ((store source).headI::store output)) := by
  cases bits:store source with
  | nil=>
    have a:=pushBit_executes output false store
    have run:=branch_executes_empty source (pushBit output true) (pushBit output false)
      store _ 1 bits a
    have restored:Function.update store source []=store := by rw [←bits,Function.update_eq_self]
    simpa only [bits,List.tail_nil,List.headI_nil,restored,show (default:Bool)=false from rfl] using run
  | cons bit rest=>
    let consumed:=Function.update store source rest
    have target:consumed output=store output := by simp [consumed,Ne.symm different]
    have a:=pushBit_executes output bit consumed
    rw [target] at a
    cases bit with
    | false=>
      exact branch_executes_false source (pushBit output true) (pushBit output false)
        store _ rest 1 bits (by simpa only [bits,List.tail_cons,List.headI_cons] using a)
    | true=>
      exact branch_executes_true source (pushBit output true) (pushBit output false)
        store _ rest 1 bits (by simpa only [bits,List.tail_cons,List.headI_cons] using a)

/-- The parity guard and halving share the same executed pop; the Boolean
answer is the actual odd-round predicate used by the protocol schedule. -/
theorem splitRound_executes (source output : Fin (extra+2)) (different:source≠output)
    (store : Store extra) (n : Nat) (encoded:store source=n.bits) :
    Executes (splitRound source output) store 2
      (Function.update (Function.update store source (n/2).bits) output
        (decide (n%2=1)::store output)) := by
  have run:=splitRound_word_executes source output different store
  rw [encoded,←Nat.div2_bits_eq_tail,Nat.div2_val,←Nat.bodd_eq_bits_head] at run
  have parity:n.bodd=decide (n%2=1) := by
    rw [Nat.mod_two_of_bodd]
    cases n.bodd <;> rfl
  rwa [parity] at run

abbrev ceilHalf (extra : Nat) (counter value scratch : Fin (extra+3)) : Routine (extra+1) :=
  sequence (DagValidation.incrementRoutine extra counter value scratch) (discardBit value)

/-- The exact core candidate `(round+1)/2`, computed on binary payloads
with a number of physical instructions linear in the label's bit length. -/
theorem ceilHalf_executes (extra : Nat) (counter value scratch : Fin (extra+3))
    (cv:counter≠value) (cs:counter≠scratch) (vs:value≠scratch)
    (store : Store (extra+1)) (emptyCounter:store counter=[]) (emptyScratch:store scratch=[])
    (n : Nat) (encoded:store value=n.bits) :
    ∃ time≤ 4*n.size+9,
      Executes (ceilHalf extra counter value scratch) store time
        (Function.update store value ((n+1)/2).bits) := by
  obtain ⟨time,bound,a⟩:=DagValidation.increment_natural extra counter value scratch cv cs vs store
    emptyCounter emptyScratch n encoded
  have b:=halve_executes value (Function.update store value (n+1).bits) (n+1) (by simp)
  rw [Function.update_idem] at b
  exact ⟨_,by omega,a.sequence b⟩

end Counting.StackMachine.ProtocolSchedule
