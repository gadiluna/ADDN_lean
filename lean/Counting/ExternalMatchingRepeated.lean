import Counting.ExternalMatchingEmitter
import Counting.StackRoutineLists

namespace Counting.External.MatchingMachine
open StackMachine StackMachine.Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

def emitRepeated (extra : Nat) (w : EdgeWorkspace extra) : Routine (extra+10) :=
  sequence (emitNatural (extra+7) (edgeNaturalRoles extra w 0))
    (sequence (emitTripleSelected (extra+6) (edgeTripleRoles extra w) (fun _=>0)) (clear (w 3)))

theorem emitRepeated_executes (extra : Nat) (w : EdgeWorkspace extra) (store : Fin (extra+12) → List Bool)
    (empty : ∀ i∈([3,7,8,9,10,11] : List (Fin 12)),store (w i)=[]) :
    ∃ time ≤ 100*((store (w 0)).length+1)^2,
      Executes (emitRepeated extra w) store time (Function.update store (w 6)
        (((Encoding.list Encoding.natural).encode
          [(store (w 0)).length,(store (w 0)).length,(store (w 0)).length]).reverse++store (w 6))) := by
  let n := (store (w 0)).length
  let code := Encoding.natural.encode n
  obtain ⟨numberTime,numberBound,numberRun⟩ := emitNatural_executes (extra+7) (edgeNaturalRoles extra w 0) store
    (empty 7 (by decide)) (empty 8 (by decide)) (empty 9 (by decide))
  let coded := Function.update store (w 3) code
  have number : Executes (emitNatural (extra+7) (edgeNaturalRoles extra w 0)) store numberTime coded := by
    simpa [edgeNaturalRoles,edgeNaturalPositions,coded,code,n,empty 3 (by decide)] using numberRun
  let edge := (Encoding.list Encoding.natural).encode [n,n,n]
  let emitted := Function.update coded (w 6) (edge.reverse++store (w 6))
  have triples := emitTripleSelected_words (extra+6) (edgeTripleRoles extra w) (fun _=>0) coded
    (by simp [edgeTripleRoles,edgeTriplePositions,coded,w.injective.eq_iff,empty 10 (by decide)])
    (by simp [edgeTripleRoles,edgeTriplePositions,coded,w.injective.eq_iff,empty 11 (by decide)])
  have triple : Executes (emitTripleSelected (extra+6) (edgeTripleRoles extra w) (fun _=>0)) coded
      (21*code.length+25) emitted := by
    have cost : 7*(code.length+code.length+code.length)+25=21*code.length+25 := by omega
    have normalized : Executes (emitTripleSelected (extra+6) (edgeTripleRoles extra w) (fun _=>0)) coded
        (7*(code.length+code.length+code.length)+25) emitted := by
      simpa [edgeTripleRoles,edgeTriplePositions,coded,emitted,edge,code,w.injective.eq_iff,
        Encoding.list,Encoding.sequence,List.append_assoc] using triples
    rw [cost] at normalized
    exact normalized
  have clearing := clear_executes (w 3) emitted
  have cleaned : Function.update emitted (w 3) []=Function.update store (w 6) (edge.reverse++store (w 6)) := by
    funext r
    by_cases e3 : r=w 3
    · subst r;simp [w.injective.eq_iff,empty 3 (by decide)]
    · simp [emitted,coded,e3,Function.update_apply]
  rw [cleaned] at clearing
  have clearTime : (emitted (w 3)).length+1=code.length+1 := by simp [emitted,coded,w.injective.eq_iff]
  rw [clearTime] at clearing
  have combined := number.sequence (triple.sequence clearing)
  refine ⟨numberTime+1+(21*code.length+25+1+(code.length+1)),?_,combined⟩
  change numberTime ≤ 20*(n+1)^2 at numberBound
  have codeBound : code.length ≤ 2*n+1 := natural_length_le n
  have lower : n+1 ≤ (n+1)^2 := Nat.le_self_pow (by decide) _
  have positive : 1 ≤ (n+1)^2 := Nat.one_le_pow _ _ (by omega)
  change _ ≤ 100*(n+1)^2
  omega

end Counting.External.MatchingMachine
