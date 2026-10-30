import Counting.ExternalCNFTerminals
import Counting.StackRoutineClearSelected

namespace Counting.External.CNFMachine
open StackMachine StackMachine.Routine
set_option backward.isDefEq.respectTransparency false

abbrev FinishWorkspace (extra : Nat) := Fin 7 ↪ Fin (extra+7)
def finishTripleRoles (extra : Nat) (w : FinishWorkspace extra) : TripleWorkspace (extra+1) :=
  (Fin.castLEEmb (by decide : 6≤7)).trans w

def finishClause (extra : Nat) (w : FinishWorkspace extra) : Routine (extra+5) :=
  sequence (emitTerminals (extra+1) (finishTripleRoles extra w))
    (sequence (clearRegisters [w 0,w 1,w 2]) (pushBit (w 6) true))

def finishResult (extra : Nat) (w : FinishWorkspace extra) (store : Fin (extra+7) → List Bool) (base terminal : Nat) :=
  Function.update (Function.update (Function.update (Function.update (Function.update store
    (w 3) ((Encoding.sequence (Encoding.list literalCodec)
      [List.replicate 3 (base,true),List.replicate 3 (terminal,false)]).reverse++store (w 3)))
    (w 0) []) (w 1) []) (w 2) []) (w 6) (true::store (w 6))

theorem finishClause_executes (extra : Nat) (w : FinishWorkspace extra)
    (store : Fin (extra+7) → List Bool) (base terminal : Nat)
    (first : store (w 0)=literalCodec.encode (base,true))
    (last : store (w 1)=literalCodec.encode (terminal,false))
    (e4 : store (w 4)=[]) (e5 : store (w 5)=[]) :
    ∃ time ≤ 100*((store (w 0)).length+(store (w 1)).length+(store (w 2)).length+1),
      Executes (finishClause extra w) store time (finishResult extra w store base terminal) := by
  have emitted := emitTerminals_executes (extra+1) (finishTripleRoles extra w) store base terminal first last e4 e5
  let word := (Encoding.sequence (Encoding.list literalCodec) [List.replicate 3 (base,true),List.replicate 3 (terminal,false)]).reverse
  let next := Function.update store (w 3) (word++store (w 3))
  let bound := (store (w 0)).length+(store (w 1)).length+(store (w 2)).length
  have bounded (r : Fin (extra+7)) (member : r∈[w 0,w 1,w 2]) : (next r).length≤bound := by
    simp only [List.mem_cons,List.not_mem_nil] at member
    rcases member with rfl|rfl|rfl|h
    all_goals first | contradiction | (simp [next,w.injective.eq_iff,bound] <;> omega)
  obtain ⟨time,timeBound,cleared⟩ := clearRegisters_selected_executes [w 0,w 1,w 2] next bound bounded
  let ready := clearedStore [w 0,w 1,w 2] next
  have advanced := pushBit_executes (w 6) true ready
  have result : Function.update ready (w 6) (true::ready (w 6))=finishResult extra w store base terminal := by
    funext r
    by_cases a : r=w 0
    · subst r;simp [ready,clearedStore,finishResult,w.injective.eq_iff]
    · by_cases b : r=w 1
      · subst r;simp [ready,clearedStore,finishResult,w.injective.eq_iff]
      · by_cases c : r=w 2
        · subst r;simp [ready,clearedStore,finishResult,w.injective.eq_iff]
        · simp [ready,clearedStore,next,finishResult,Function.update_apply,a,b,c,word,w.injective.eq_iff]
  rw [result] at advanced
  have combined := emitted.sequence (cleared.sequence advanced)
  refine ⟨21*((literalCodec.encode (base,true)).length+(literalCodec.encode (terminal,false)).length)+51+1+(time+1+1),?_,combined⟩
  change time≤3*(bound+2) at timeBound
  rw [←first,←last]
  dsimp [bound] at timeBound
  omega

end Counting.External.CNFMachine
