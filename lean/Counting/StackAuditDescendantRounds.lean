import Counting.StackAuditPropagationRounds
import Counting.StackSubtractLength

namespace Counting.StackMachine.AuditDescendant
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

def lastRoundRoles : Fin 44 ↪ Fin 48 :=
  ⟨![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,
      22,23,24,25,26,27,28,29,30,31,32,33,42,35,36,37,41,39,44,38,34,47],by decide⟩

def anchorRoundRoles : Fin 44 ↪ Fin 48 :=
  ⟨![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,
      22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,44,42,40,47],by decide⟩

def roundWorkspace : Finset (Fin 48) := {0,2,3,4,5,6,7,8,9,10,13,38,42,47}

/-- Both unary conversions use the stored-node budget. Subtraction consumes
only these bounded words and leaves the original binary labels untouched. -/
def prepareRounds : Routine 46 := sequence
  (relocate AuditPropagation.preparePropagationRounds lastRoundRoles)
  (sequence (relocate AuditPropagation.preparePropagationRounds anchorRoundRoles)
    (sequence (subtractLength 44 42 38 0 47) (clear 42)))

theorem prepareRounds_executes (store : Store 46) (last anchor n : Nat)
    (lastAt : store 34=last.bits) (anchorAt : store 40=anchor.bits)
    (countAt : store 44=List.replicate n true)
    (empty : ∀ r : Fin 48,r∈roundWorkspace → store r=[]) :
    ∃ time ≤ 2100*(n+last.size+anchor.size+1)^3,
      Executes prepareRounds store time
        (Function.update store 38 (List.replicate (min last n-min anchor n) true)) := by
  let lastStore : Store 42:=store ∘ lastRoundRoles
  obtain ⟨lastTime,lastBound,a⟩:=AuditPropagation.preparePropagationRounds_executes lastStore last n
    (by simp [lastStore,lastRoundRoles,lastAt]) (by simp [lastStore,lastRoundRoles,countAt]) (by
      intro r member;fin_cases r <;> simp_all [lastStore,lastRoundRoles,roundWorkspace])
  let lastReady:=Function.update store 38 (List.replicate (min last n) true)
  have lastRun : Executes (relocate AuditPropagation.preparePropagationRounds lastRoundRoles)
      store lastTime lastReady := by
    apply relocate_executes_frame _ lastRoundRoles store lastReady lastStore _ lastTime rfl _ _ a
    · intro r;fin_cases r <;> simp [lastReady,lastStore,lastRoundRoles]
    · intro r outside
      have n38 : r≠38 := by intro same;subst r;exact outside 41 rfl
      simp [lastReady,n38]
  let anchorStore : Store 42:=lastReady ∘ anchorRoundRoles
  obtain ⟨anchorTime,anchorBound,b⟩:=AuditPropagation.preparePropagationRounds_executes anchorStore anchor n
    (by simp [anchorStore,anchorRoundRoles,lastReady,anchorAt])
    (by simp [anchorStore,anchorRoundRoles,lastReady,countAt]) (by
      intro r member;fin_cases r <;> simp_all [anchorStore,anchorRoundRoles,lastReady,roundWorkspace])
  let bothReady:=Function.update lastReady 42 (List.replicate (min anchor n) true)
  have anchorRun : Executes (relocate AuditPropagation.preparePropagationRounds anchorRoundRoles)
      lastReady anchorTime bothReady := by
    apply relocate_executes_frame _ anchorRoundRoles lastReady bothReady anchorStore _ anchorTime rfl _ _ b
    · intro r;fin_cases r <;> simp [bothReady,anchorStore,anchorRoundRoles]
    · intro r outside
      have n42 : r≠42 := by intro same;subst r;exact outside 41 rfl
      simp [bothReady,n42]
  have c:=subtractLength_executes 44 (42:Fin 48) 38 0 47
    (by decide) (by decide) (by decide) (by decide) bothReady
    (by simp [bothReady,lastReady,empty 0 (by decide +kernel)])
    (by simp [bothReady,lastReady,empty 47 (by decide +kernel)])
  have source : bothReady 42=List.replicate (min anchor n) true := by simp [bothReady]
  have target : bothReady 38=List.replicate (min last n) true := by simp [bothReady,lastReady]
  rw [source,target,List.length_replicate,List.drop_replicate] at c
  let difference:=Function.update bothReady 38 (List.replicate (min last n-min anchor n) true)
  have d:=clear_executes (42:Fin 48) difference
  have temporary : difference 42=List.replicate (min anchor n) true := by simp [difference,bothReady]
  rw [temporary,List.length_replicate] at d
  have final : Function.update difference 42 []=
      Function.update store 38 (List.replicate (min last n-min anchor n) true) := by
    funext r
    by_cases r38:r=38 <;> by_cases r42:r=42 <;>
      simp [difference,bothReady,lastReady,r38,r42,empty 42 (by decide +kernel)]
  rw [final] at d
  let K:=n+last.size+anchor.size+1
  have lastLimit : lastTime ≤ 1000*K^3 := lastBound.trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp only [K];omega) 3))
  have anchorLimit : anchorTime ≤ 1000*K^3 := anchorBound.trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp only [K];omega) 3))
  have positive : 1 ≤ K := by dsimp only [K];omega
  have linear : K ≤ K^3:=Nat.le_self_pow (by decide) _
  have one : 1 ≤ K^3:=Nat.one_le_pow _ _ positive
  have short : min anchor n ≤ K := by dsimp only [K];omega
  refine ⟨_,?_,lastRun.sequence (anchorRun.sequence (c.sequence d))⟩
  change lastTime+1+(anchorTime+1+(7*min anchor n+4+1+(min anchor n+1))) ≤ 2100*K^3
  omega

/-- Once the opening depth check has established the node-count bound,
the bounded physical subtraction is exactly the required ascent length. -/
theorem prepareRounds_exact (store : Store 46) (last anchor n : Nat)
    (fits : last ≤ n) (lastAt : store 34=last.bits) (anchorAt : store 40=anchor.bits)
    (countAt : store 44=List.replicate n true)
    (empty : ∀ r : Fin 48,r∈roundWorkspace → store r=[]) :
    ∃ time ≤ 2100*(n+last.size+anchor.size+1)^3,
      Executes prepareRounds store time (Function.update store 38 (List.replicate (last-anchor) true)) := by
  have difference : min last n-min anchor n=last-anchor := by omega
  simpa only [difference] using prepareRounds_executes store last anchor n lastAt anchorAt countAt empty

end Counting.StackMachine.AuditDescendant
