import Counting.StackLookupPreserving
import Counting.StackEncodingBranch
import Counting.RealizabilityBitGraph

namespace Counting.StackMachine.RealizabilityCheck
open Routine EncodingPrograms
set_option backward.isDefEq.respectTransparency false

/-- Lookup in the flat Boolean graph storage, including its specified false
default. Both the source and length-coded index survive the physical scan. -/
def bitLookup (extra : Nat) (roles : Fin 7 ↪ Fin (extra+7)) : Routine (extra+5):=
  sequence (Lookup.preservingLookup extra roles)
    (branchRoutine (roles 3) (skip (extra+5)) (pushBit (roles 2) false))

theorem bitLookup_executes (extra : Nat) (roles : Fin 7 ↪ Fin (extra+7))
    (store : Store (extra+5))
    (e4 : store (roles 4)=[]) (e5 : store (roles 5)=[]) (e6 : store (roles 6)=[]) :
    ∃ time ≤ 6*(store (roles 0)).length+7*(store (roles 1)).length+16,
      Executes (bitLookup extra roles) store time
        (Function.update store (roles 2)
          (RealizabilityVerifier.BitGraph.bitAt (store (roles 0)) (store (roles 1)).length::store (roles 2))):=by
  have reading:=Lookup.preservingLookup_executes extra roles store e4 e5 e6
  have bound:=Lookup.lookupCost_le (store (roles 0)) (store (roles 1))
  let selected:=(store (roles 0))[(store (roles 1)).length]?
  let ready:=Function.update (Function.update store (roles 2) (selected.toList++store (roles 2)))
    (roles 3) (selected.isSome::store (roles 3))
  cases found : selected with
  | none=>
    have result : Function.update ready (roles 3) (store (roles 3))=store:=by
      simp [ready,found,Function.update_eq_self]
    have body:=pushBit_executes (roles 2) false store
    have branched:=branch_executes_false (roles 3) (skip (extra+5)) (pushBit (roles 2) false)
      ready _ (store (roles 3)) 1 (by simp [ready,found]) (by rw [result];exact body)
    refine ⟨Lookup.lookupCost (store (roles 0)) (store (roles 1))+1+(1+1),by omega,?_⟩
    have actual : RealizabilityVerifier.BitGraph.bitAt (store (roles 0)) (store (roles 1)).length=false:=by
      change selected.getD false=false
      rw [found]
      rfl
    rw [actual]
    exact reading.sequence branched
  | some bit=>
    let result:=Function.update store (roles 2) (bit::store (roles 2))
    have restored : Function.update ready (roles 3) (store (roles 3))=result:=by
      funext r
      by_cases atFlag : r=roles 3
      · subst r;simp [ready,result,roles.injective.eq_iff]
      · simp [ready,result,found,Function.update_apply,atFlag]
    have branched:=branch_executes_true (roles 3) (skip (extra+5)) (pushBit (roles 2) false)
      ready result (store (roles 3)) 0 (by simp [ready,found])
      (by rw [restored];exact Routine.skip_executes result)
    refine ⟨Lookup.lookupCost (store (roles 0)) (store (roles 1))+1+(1+0),by omega,?_⟩
    have actual : RealizabilityVerifier.BitGraph.bitAt (store (roles 0)) (store (roles 1)).length=bit:=by
      change selected.getD false=bit
      rw [found]
      rfl
    rw [actual]
    exact reading.sequence branched

end Counting.StackMachine.RealizabilityCheck
