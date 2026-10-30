import Counting.StackRealizabilityReachActive

namespace Counting.StackMachine.RealizabilityCheck
open Routine
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def rowSourceRoles : Fin 18 ↪ Fin 24 where
  toFun r:=⟨r.val,by omega⟩
  inj':=by intro a b equal;apply Fin.ext;exact congrArg (fun r:Fin 24=>r.val) equal

def rowSeen (width : Nat) (arcs : List Bool) (source : Nat) : List Bool:=
  reachIterations width arcs width (reachInitialValues source 0 width)

theorem reachIterations_length (width count : Nat) (arcs seen : List Bool) (length : seen.length=width) :
    (reachIterations width arcs count seen).length=width:=by
  induction count generalizing seen with
  | zero=>exact length
  | succ count ih=>exact ih _ (RealizabilityVerifier.BitGraph.reachPass_length ..)

@[simp] theorem rowSeen_length (width : Nat) (arcs : List Bool) (source : Nat) :
    (rowSeen width arcs source).length=width:=
  reachIterations_length width width arcs (reachInitialValues source 0 width) (reachInitialValues_length source 0 width)

/-- Working-store invariant. Graph data, source counter, active mask, global
answer and outer counter may be nonempty; all private registers are empty. -/
def RowEmpty (store : Store 22) : Prop:=
  ∀ r : Fin 24, r ≠ 0 → r ≠ 2 → r ≠ 17 → r ≠ 18 → r ≠ 19 → r ≠ 23 → store r=[]

def rowSource : Routine 22:=mapRegisters rowSourceRoles reachSourceRoutine

theorem rowSource_executes (store : Store 22) (empty : RowEmpty store) :
    ∃ time ≤ 200000*((store 0).length+(store 2).length+(store 17).length+1)^5,
      Executes rowSource store time (Function.update store 1 (rowSeen (store 2).length (store 0) (store 17).length)):=by
  let original:Store 16:=store ∘ rowSourceRoles
  have originalEmpty : ∀ r : Fin 18, r ≠ 0 → r ≠ 2 → r ≠ 17 → original r=[]:=by
    intro r n0 n2 n17
    apply empty (rowSourceRoles r)
    · intro equal;apply n0;exact Fin.ext (congrArg (fun t : Fin 24=>t.val) equal)
    · intro equal;apply n2;exact Fin.ext (congrArg (fun t : Fin 24=>t.val) equal)
    · intro equal;apply n17;exact Fin.ext (congrArg (fun t : Fin 24=>t.val) equal)
    · intro equal;have h:=congrArg Fin.val equal;dsimp [rowSourceRoles] at h;omega
    · intro equal;have h:=congrArg Fin.val equal;dsimp [rowSourceRoles] at h;omega
    · intro equal;have h:=congrArg Fin.val equal;dsimp [rowSourceRoles] at h;omega
  obtain ⟨time,bound,ran⟩:=reachSource_executes original originalEmpty
  refine ⟨time,bound,?_⟩
  apply relocate_executes_frame reachSourceRoutine rowSourceRoles store _ original _ time rfl _ _ ran
  · intro r
    fin_cases r <;> simp [original,rowSourceRoles,reachSourceBits,rowSeen]
  · intro r outside
    have ne : r≠1:=by intro same;subst r;exact outside 1 rfl
    simp [ne]

def rowActiveRoles : Fin 7 ↪ Fin 24:=⟨![18,1,2,21,20,8,12],by decide⟩
def rowActive : Routine 22:=mapRegisters rowActiveRoles activeCheck

theorem rowActive_executes (store : Store 22) (value : Bool) (tail : List Bool)
    (accumulated : store 21=value::tail) (e20 : store 20=[]) (e8 : store 8=[]) (e12 : store 12=[])
    (length : (store 1).length=(store 2).length) :
    ∃ time ≤ 6*(store 18).length+11*(store 2).length+10,
      Executes rowActive store time (Function.update (Function.update store 1 [])
        21 (implicationFold (store 2).length (store 18) (store 1) value::tail)):=by
  let original:Store 5:=store ∘ rowActiveRoles
  obtain ⟨time,bound,ran⟩:=activeCheck_executes original value tail accumulated e20 e8 e12
  have dropped : (original 1).drop (original 2).length=[]:=by
    change (store 1).drop (store 2).length=[]
    rw [←length,List.drop_length]
  rw [dropped] at ran
  refine ⟨time,bound,?_⟩
  apply relocate_executes_frame activeCheck rowActiveRoles store _ original _ time rfl _ _ ran
  · intro r
    fin_cases r <;> simp [original,rowActiveRoles]
  · intro r outside
    have n1 : r≠1:=by intro same;subst r;exact outside 1 rfl
    have n21 : r≠21:=by intro same;subst r;exact outside 3 rfl
    simp [n1,n21]

def rowReachable (store : Store 22) : Bool:=
  implicationFold (store 2).length (store 18)
    (rowSeen (store 2).length (store 0) (store 17).length) true

def rowPrepare : Routine 22:=sequence rowSource (sequence (pushBit 21 true) rowActive)

theorem rowPrepare_executes (store : Store 22) (empty : RowEmpty store) :
    ∃ time ≤ 201000*((store 0).length+(store 18).length+(store 2).length+(store 17).length+1)^5,
      Executes rowPrepare store time (Function.update store 21 [rowReachable store]):=by
  obtain ⟨sourceTime,sourceBound,sourceRun⟩:=rowSource_executes store empty
  let reached:=Function.update store 1 (rowSeen (store 2).length (store 0) (store 17).length)
  have initializing:=pushBit_executes (21:Fin 24) true reached
  have empty21 : reached 21=[]:=by simp [reached,empty 21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  rw [empty21] at initializing
  let prepared:=Function.update reached 21 [true]
  obtain ⟨activeTime,activeBound,activeRun⟩:=rowActive_executes prepared true [] (by simp [prepared])
    (by simp [prepared,reached,empty 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)])
    (by simp [prepared,reached,empty 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)])
    (by simp [prepared,reached,empty 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)])
    (by simp [prepared,reached])
  have final : Function.update (Function.update prepared 1 []) 21
      (implicationFold (prepared 2).length (prepared 18) (prepared 1) true::[])=
        Function.update store 21 [rowReachable store]:=by
    funext r
    by_cases n1 : r=1 <;> by_cases n21 : r=21 <;>
      simp [prepared,reached,rowReachable,n1,n21,
        empty 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  rw [final] at activeRun
  have activeLimit : activeTime ≤ 6*(store 18).length+11*(store 2).length+10:=by
    simpa [prepared,reached] using activeBound
  let S:=(store 0).length+(store 18).length+(store 2).length+(store 17).length+1
  have sourceLimit : sourceTime ≤ 200000*S^5:=by
    apply sourceBound.trans
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by dsimp only [S];omega) 5)
  have linear : S ≤ S^5:=Nat.le_self_pow (by decide) _
  have one : 1 ≤ S^5:=Nat.one_le_pow _ _ (by dsimp only [S];omega)
  exact ⟨_,by change _ ≤ 201000*S^5;dsimp only [S] at sourceLimit linear one ⊢;omega,
    sourceRun.sequence (initializing.sequence activeRun)⟩

end Counting.StackMachine.RealizabilityCheck
