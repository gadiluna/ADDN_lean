import Counting.ExternalCoverInputOrder
import Counting.StackRoutineMove

namespace Counting.External.CoverInputValidation
open StackMachine StackMachine.Routine StackMachine.EncodingPrograms SATVerification
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

def tripleScratch : List (Fin 32):=MatchingInputValidation.indexScratch++[20,30,31]

def tripleGuard (extra : Nat) (w : SATWorkspace extra) : Routine (extra+30) :=
  sequence (ofProgram (ListPrograms.copyProgram (extra+29) (w 0) (w 31) (w 30)))
    (sequence (MatchingInputValidation.tripleGuard extra w)
      (sequence (clear (w 0))
        (sequence (move (extra+29) (w 31) (w 0) (w 30)) (orderedTriple extra w))))

theorem tripleGuard_executes (extra : Nat) (w : SATWorkspace extra)
    (store : Fin (extra+32) → List Bool) (a b c : Nat) (accepted : Bool) (suffix tail : List Bool)
    (source : store (w 0)=(Encoding.list Encoding.natural).encode [a,b,c]++suffix)
    (status : store (w 1)=accepted::tail) (empty : ∀ i∈tripleScratch,store (w i)=[]) :
    ∃ time ≤ 1300*((store (w 0)).length+(store (w 17)).length+1)^3,
      Executes (tripleGuard extra w) store time
        (Function.update (Function.update store (w 0) suffix) (w 1)
          ((accepted && ([a,b,c].all (fun value=>decide (value < (store (w 17)).length)) &&
            decide (a < b ∧ b < c)))::tail)) := by
  let input:=store (w 0)
  let ranged:=[a,b,c].all (fun value=>decide (value < (store (w 17)).length))
  have copying:=copy_executes (extra+29) (w 0) (w 31) (w 30)
    (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff])
    store (empty 30 (by simp [tripleScratch]))
  rw [empty 31 (by simp [tripleScratch]),List.append_nil] at copying
  let saved:=Function.update store (w 31) input
  have savedEmpty (i : Fin 32) (member : i∈MatchingInputValidation.indexScratch) : saved (w i)=[] := by
    have n31 : i≠31:=by intro same;subst i;simp [MatchingInputValidation.indexScratch] at member
    simpa [saved,w.injective.eq_iff,n31] using empty i (by simp [tripleScratch,member])
  obtain ⟨rt,rb,rr⟩:=MatchingInputValidation.tripleGuard_executes extra w saved a b c accepted suffix tail
    (by simp [saved,w.injective.eq_iff,source]) (by simp [saved,w.injective.eq_iff,status]) savedEmpty
  have sourceSaved : saved (w 0)=input:=by simp [saved,w.injective.eq_iff,input]
  have universeSaved : saved (w 17)=store (w 17):=by simp [saved,w.injective.eq_iff]
  rw [sourceSaved,universeSaved] at rb
  rw [universeSaved] at rr
  let checked:=Function.update (Function.update saved (w 0) suffix) (w 1) ((accepted && ranged)::tail)
  have clearing:=clear_executes (w 0) checked
  have sourceChecked : checked (w 0)=suffix:=by simp [checked,w.injective.eq_iff]
  rw [sourceChecked] at clearing
  let cleared:=Function.update checked (w 0) []
  have moving:=move_executes (extra+29) (w 31) (w 0) (w 30)
    (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) cleared
    (by simp [cleared,checked,saved,w.injective.eq_iff,empty,tripleScratch])
  have originalAt : cleared (w 31)=input:=by simp [cleared,checked,saved,w.injective.eq_iff]
  have clearedAt : cleared (w 0)=[]:=by simp [cleared]
  rw [originalAt,clearedAt,List.append_nil] at moving
  let restored:=Function.update (Function.update cleared (w 0) input) (w 31) []
  have restoredSource : restored (w 0)=input:=by simp [restored,w.injective.eq_iff]
  have restoredEmpty (i : Fin 32) (member : i∈orderScratch) : restored (w i)=[] := by
    have n0 : i≠0:=by intro same;subst i;simp [orderScratch] at member
    have n1 : i≠1:=by intro same;subst i;simp [orderScratch] at member
    have n31 : i≠31:=by intro same;subst i;simp [orderScratch] at member
    have included : i∈tripleScratch := by
      simp only [orderScratch,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals simp [tripleScratch,MatchingInputValidation.indexScratch]
    simpa [restored,cleared,checked,saved,w.injective.eq_iff,n0,n1,n31] using empty i included
  obtain ⟨ot,ob,orr⟩:=orderedTriple_executes extra w restored a b c (accepted && ranged) suffix tail
    (restoredSource.trans source) (by simp [restored,cleared,checked,w.injective.eq_iff]) restoredEmpty
  rw [restoredSource] at ob
  have final : Function.update (Function.update restored (w 0) suffix)
      (w 1) (((accepted && ranged) && decide (a < b ∧ b < c))::tail)=
      Function.update (Function.update store (w 0) suffix)
        (w 1) ((accepted && ranged && decide (a < b ∧ b < c))::tail) := by
    funext r
    by_cases n1 : r=w 1
    · subst r;simp
    · by_cases n0 : r=w 0
      · subst r;simp [w.injective.eq_iff]
      · by_cases n31 : r=w 31
        · subst r;simp [restored,w.injective.eq_iff,empty,tripleScratch]
        · simp [restored,cleared,checked,saved,n0,n1,n31]
  rw [final] at orr
  have executed:=copying.sequence (rr.sequence (clearing.sequence (moving.sequence orr)))
  refine ⟨5*input.length+2+1+(rt+1+(suffix.length+1+1+(6*input.length+4+1+ot))),?_,by simpa +instances only [tripleGuard,input,ranged,Bool.and_assoc,ListPrograms.copyProgram] using executed⟩
  have suffixBound : suffix.length ≤ input.length:=by dsimp [input];rw [source];simp only [List.length_append];omega
  have linear : input.length+(store (w 17)).length+1 ≤ (input.length+(store (w 17)).length+1)^3 :=
    Nat.le_self_pow (by decide) _
  change _ ≤ 1300*(input.length+(store (w 17)).length+1)^3
  omega

end Counting.External.CoverInputValidation
