import Counting.StackRealizabilityReachInitial

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def sourceInitialRoles : Fin 10 ↪ Fin 18:=⟨![2,17,14,16,4,5,6,12,15,1],by decide⟩
def sourceIterationRoles : Fin 17 ↪ Fin 18 where
  toFun r:=⟨r.val,by omega⟩
  inj':=by intro a b equal;apply Fin.ext;exact congrArg (fun r:Fin 18=>r.val) equal

def sourceInitial : Routine 16:=mapRegisters sourceInitialRoles reachInitialRoutine
def sourceIteration : Routine 16:=mapRegisters sourceIterationRoles (forEach 8 reachStepRoutine)

theorem sourceInitial_executes (store : Store 16)
    (empty : ∀ r : Fin 18, r ≠ 0 → r ≠ 2 → r ≠ 17 → store r = []) :
    ∃ time ≤ 40*((store 2).length+(store 17).length+1)^2,
      Executes sourceInitial store time (Function.update store 1 (reachInitialValues (store 17).length 0 (store 2).length)):=by
  let original:Store 8:=store ∘ sourceInitialRoles
  have e (r : Fin 18) (a : r≠0) (b : r≠2) (c : r≠17):=empty r a b c
  obtain ⟨time,bound,ran⟩:=reachInitial_executes original
    (e 14 (by decide) (by decide) (by decide)) (e 16 (by decide) (by decide) (by decide))
    (e 4 (by decide) (by decide) (by decide)) (e 5 (by decide) (by decide) (by decide))
    (e 6 (by decide) (by decide) (by decide)) (e 12 (by decide) (by decide) (by decide))
    (e 15 (by decide) (by decide) (by decide)) (e 1 (by decide) (by decide) (by decide))
  refine ⟨time,bound,?_⟩
  apply relocate_executes_frame reachInitialRoutine sourceInitialRoles store _ original _ time rfl _ _ ran
  · intro r
    fin_cases r <;> simp [original,sourceInitialRoles]
  · intro r outside
    have ne : r≠1:=by intro same;subst r;exact outside 9 rfl
    simp [ne]

theorem sourceIteration_executes (store : Store 16) (counter : List Bool) (counted : store 8=counter)
    (seenLength : (store 1).length=(store 2).length)
    (empty : ∀ r : Fin 18, r ≠ 0 → r ≠ 1 → r ≠ 2 → r ≠ 8 → r ≠ 17 → store r = []) :
    ∃ time ≤ counter.length*(11000*((store 0).length+2*(store 2).length+1)^4+2)+1,
      Executes sourceIteration store time (Function.update (Function.update store 8 []) 1
        (reachIterations (store 2).length (store 0) counter.length (store 1))):=by
  let original:Store 15:=store ∘ sourceIterationRoles
  have e (r : Fin 18) (a : r≠0) (b : r≠1) (c : r≠2) (d : r≠8) (f : r≠17):=empty r a b c d f
  obtain ⟨time,bound,ran⟩:=reachIteration_executes original counter counted (store 2).length
    seenLength.le (le_refl _)
    (e 3 (by decide) (by decide) (by decide) (by decide) (by decide))
    (e 4 (by decide) (by decide) (by decide) (by decide) (by decide))
    (e 5 (by decide) (by decide) (by decide) (by decide) (by decide))
    (e 6 (by decide) (by decide) (by decide) (by decide) (by decide))
    (e 7 (by decide) (by decide) (by decide) (by decide) (by decide))
    (e 9 (by decide) (by decide) (by decide) (by decide) (by decide))
    (e 10 (by decide) (by decide) (by decide) (by decide) (by decide))
    (e 11 (by decide) (by decide) (by decide) (by decide) (by decide))
    (e 12 (by decide) (by decide) (by decide) (by decide) (by decide))
    (e 13 (by decide) (by decide) (by decide) (by decide) (by decide))
    (e 14 (by decide) (by decide) (by decide) (by decide) (by decide))
    (e 15 (by decide) (by decide) (by decide) (by decide) (by decide))
    (e 16 (by decide) (by decide) (by decide) (by decide) (by decide))
  refine ⟨time,?_,?_⟩
  · simpa [original,sourceIterationRoles,Nat.two_mul,Nat.add_assoc] using bound
  · apply relocate_executes_frame (forEach 8 reachStepRoutine) sourceIterationRoles store _ original
      (reachIterationStore original counter.length) time rfl _ _ ran
    · intro r
      fin_cases r <;> simp [original,sourceIterationRoles,reachIterationStore]
    · intro r outside
      have n1 : r≠1:=by intro same;subst r;exact outside 1 rfl
      have n8 : r≠8:=by intro same;subst r;exact outside 8 rfl
      simp [n1,n8]

/-- Full bounded search from a source slot. Width and source are explicit
length counters, independent of certificate population counts. -/
def reachSourceRoutine : Routine 16:=sequence sourceInitial
  (sequence (ofProgram (ListPrograms.copyProgram 15 2 8 12)) sourceIteration)

def reachSourceBits (store : Store 16) : List Bool:=
  reachIterations (store 2).length (store 0) (store 2).length
    (reachInitialValues (store 17).length 0 (store 2).length)

theorem reachSource_executes (store : Store 16)
    (empty : ∀ r : Fin 18, r ≠ 0 → r ≠ 2 → r ≠ 17 → store r = []) :
    ∃ time ≤ 200000*((store 0).length+(store 2).length+(store 17).length+1)^5,
      Executes reachSourceRoutine store time (Function.update store 1 (reachSourceBits store)):=by
  obtain ⟨initialTime,initialBound,initialRun⟩:=sourceInitial_executes store empty
  let initialized:=Function.update store 1 (reachInitialValues (store 17).length 0 (store 2).length)
  have copying:=copy_executes 15 2 8 12 (by decide) (by decide) (by decide) initialized
    (by simp [initialized,empty 12 (by decide) (by decide) (by decide)])
  have widthAt : initialized 2=store 2:=by simp [initialized]
  have countAt : initialized 8=[]:=by simp [initialized,empty 8 (by decide) (by decide) (by decide)]
  rw [widthAt,countAt,List.append_nil] at copying
  let prepared:=Function.update initialized 8 (store 2)
  obtain ⟨loopTime,loopBound,loopRun⟩:=sourceIteration_executes prepared (store 2)
    (by simp [prepared]) (by simp [prepared,initialized])
    (by intro r n0 n1 n2 n8 n17;simp [prepared,initialized,n1,n8,empty r n0 n2 n17])
  have final : Function.update (Function.update prepared 8 []) 1
      (reachIterations (prepared 2).length (prepared 0) (store 2).length (prepared 1))=
        Function.update store 1 (reachSourceBits store):=by
    funext r
    by_cases n1 : r=1 <;> by_cases n8 : r=8 <;>
      simp [prepared,initialized,reachSourceBits,n1,n8,empty 8 (by decide) (by decide) (by decide)]
  rw [final] at loopRun
  have loopLimit : loopTime ≤ (store 2).length*(11000*((store 0).length+2*(store 2).length+1)^4+2)+1:=by
    simpa [prepared,initialized] using loopBound
  let S:=(store 0).length+(store 2).length+(store 17).length+1
  have positive : 1 ≤ S:=by dsimp only [S];omega
  have width : (store 2).length ≤ S:=by dsimp only [S];omega
  have base : (store 0).length+2*(store 2).length+1 ≤ 2*S:=by dsimp only [S];omega
  have initialBase : (store 2).length+(store 17).length+1 ≤ S:=by dsimp only [S];omega
  have initialLimit : initialTime ≤ 40*S^5:=by
    apply initialBound.trans
    exact Nat.mul_le_mul_left _ ((Nat.pow_le_pow_left initialBase 2).trans (Nat.pow_le_pow_right positive (by decide)))
  have loopLimit' : loopTime ≤ 176000*S^5+2*S+1:=by
    have b : loopTime ≤ S*(11000*(2*S)^4+2)+1:=by
      apply loopLimit.trans
      exact Nat.add_le_add_right (Nat.mul_le_mul width
        (Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left base 4)) 2)) 1
    have expansion (x : Nat) : x*(11000*(2*x)^4+2)+1=176000*x^5+2*x+1:=by ring
    exact expansion S ▸ b
  have linear : S ≤ S^5:=Nat.le_self_pow (by decide) _
  have one : 1 ≤ S^5:=Nat.one_le_pow _ _ positive
  exact ⟨_,by change _ ≤ 200000*S^5;dsimp only [S] at initialLimit loopLimit' linear one ⊢;omega,
    initialRun.sequence (copying.sequence loopRun)⟩

theorem reachSourceBits_iterate (store : Store 16) (inside : (store 17).length<(store 2).length) :
    reachSourceBits store=RealizabilityVerifier.BitGraph.iterate (store 2).length (store 0)
      ⟨(store 17).length,inside⟩ (store 2).length:=by
  unfold reachSourceBits
  rw [reachInitialValues_initial _ ⟨(store 17).length,inside⟩]
  simpa only [RealizabilityVerifier.BitGraph.iterate,Nat.zero_add] using
    reachIterations_iterate (store 2).length (store 0) ⟨(store 17).length,inside⟩ 0 (store 2).length

end Counting.StackMachine.RealizabilityCheck
