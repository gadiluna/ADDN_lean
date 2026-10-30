import Counting.ExternalCoordinateCenter
import Counting.StackAddScaledDifference
import Counting.StackRoutineMove

namespace Counting.External.MatchingDimensions
open StackMachine StackMachine.Routine CookLevin.StackGenerator
set_option backward.isDefEq.respectTransparency false

abbrev Workspace (extra : Nat) := Fin 12 ↪ Fin (extra+12)
def slots (n m : Nat) := n*(3*m+1)
def order (n m : Nat) := 2*slots n m
def garbage (n m : Nat) := slots n m-m
def edges (n m : Nat) := order n m+3*m+garbage n m*order n m

def slotSelection : Fin 6 ↪ Fin 12 := ⟨![0,2,7,3,9,10],by decide⟩
def differenceSelection : Fin 6 ↪ Fin 12 := ⟨![3,1,5,8,9,10],by decide⟩
def productSelection : Fin 6 ↪ Fin 12 := ⟨![5,4,7,8,9,10],by decide⟩
def Workspace.slotRoles (w : Workspace extra) : PolynomialWorkspace (extra+6) := slotSelection.trans w
def Workspace.differenceRoles (w : Workspace extra) : PolynomialWorkspace (extra+6) := differenceSelection.trans w
def Workspace.productRoles (w : Workspace extra) : PolynomialWorkspace (extra+6) := productSelection.trans w

/-- Only the explicit variable/clause counters are inputs. All dimensions
and the number of emitted sparse edges are calculated by real unary loops. -/
def routine (extra : Nat) (w : Workspace extra) : Routine (extra+10) :=
  sequence (scaleLength (extra+9) (w 1) (w 2) (w 10) 3)
    (sequence (pushBit (w 2) true)
      (sequence (centerRoutine (extra+6) w.slotRoles)
        (sequence (scaleLength (extra+9) (w 3) (w 4) (w 10) 2)
          (sequence (addScaledDifference (extra+6) w.differenceRoles 1)
            (sequence (centerRoutine (extra+6) w.productRoles)
              (sequence (scaleLength (extra+9) (w 1) (w 6) (w 10) 3)
                (sequence (scaleLength (extra+9) (w 4) (w 6) (w 10) 1)
                  (move (extra+9) (w 8) (w 6) (w 10)))))))))

def result (w : Workspace extra) (n m : Nat) (store : Fin (extra+12) → List Bool) :=
  Function.update (Function.update (Function.update (Function.update (Function.update store
    (w 2) (List.replicate (3*m+1) true)) (w 3) (List.replicate (slots n m) true))
    (w 4) (List.replicate (order n m) true)) (w 5) (List.replicate (garbage n m) true))
    (w 6) (List.replicate (edges n m) true)

def cost (n m : Nat) :=
  20*slots n m+15*garbage n m+11*(garbage n m*order n m)+5*order n m+9*n+37*m+67

theorem routine_executes (extra : Nat) (w : Workspace extra) (n m : Nat)
    (store : Fin (extra+12) → List Bool)
    (nValue : store (w 0)=List.replicate n true) (mValue : store (w 1)=List.replicate m true)
    (empty : ∀ i : Fin 12,i≠0 → i≠1 → store (w i)=[]) :
    Executes (routine extra w) store (cost n m) (result w n m store) := by
  let s₁ := Function.update store (w 2) (List.replicate (3*m) true)
  let s₂ := Function.update store (w 2) (List.replicate (3*m+1) true)
  let s₃ := Function.update s₂ (w 3) (List.replicate (slots n m) true)
  let s₄ := Function.update s₃ (w 4) (List.replicate (order n m) true)
  let s₅ := Function.update s₄ (w 5) (List.replicate (garbage n m) true)
  let s₆ := Function.update s₅ (w 8) (List.replicate (garbage n m*order n m) true)
  let s₇ := Function.update s₆ (w 6) (List.replicate (3*m) true)
  let s₈ := Function.update s₆ (w 6) (List.replicate (order n m+3*m) true)
  have a : Executes (scaleLength (extra+9) (w 1) (w 2) (w 10) 3) store (3*(5*m+3)) s₁ := by
    simpa only [mValue,List.length_replicate,empty 2 (by decide) (by decide),List.append_nil,s₁] using
      scaleLength_executes (extra+9) (w 1) (w 2) (w 10)
        (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff])
        3 store (empty 10 (by decide) (by decide))
  have b : Executes (pushBit (w 2) true) s₁ 1 s₂ := by
    simpa only [s₁,s₂,Function.update_self,Function.update_idem,List.replicate_succ] using
      pushBit_executes (w 2) true s₁
  have c : Executes (centerRoutine (extra+6) w.slotRoles) s₂ (centerCost n (3*m+1) 0) s₃ := by
    have run := centerRoutine_executes (extra+6) w.slotRoles n (3*m+1) 0 s₂
      (by simp [Workspace.slotRoles,slotSelection,s₂,w.injective.eq_iff,nValue])
      (by simp [Workspace.slotRoles,slotSelection,s₂])
      (by simp [Workspace.slotRoles,slotSelection,s₂,w.injective.eq_iff,empty])
      (by simp [Workspace.slotRoles,slotSelection,s₂,w.injective.eq_iff,empty])
      (by simp [Workspace.slotRoles,slotSelection,s₂,w.injective.eq_iff,empty])
      (by simp [Workspace.slotRoles,slotSelection,s₂,w.injective.eq_iff,empty])
    simpa [s₃,slots,Workspace.slotRoles,slotSelection] using run
  have d : Executes (scaleLength (extra+9) (w 3) (w 4) (w 10) 2) s₃ (2*(5*slots n m+3)) s₄ := by
    have run := scaleLength_executes (extra+9) (w 3) (w 4) (w 10)
      (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) 2 s₃
      (by simp [s₃,s₂,w.injective.eq_iff,empty])
    simpa [s₄,s₃,s₂,order,w.injective.eq_iff,empty] using run
  have e : Executes (addScaledDifference (extra+6) w.differenceRoles 1) s₄
      (addScaledDifferenceCost (slots n m) m 1) s₅ := by
    have run := addScaledDifference_executes (extra+6) w.differenceRoles 1 s₄
      (by simp [Workspace.differenceRoles,differenceSelection,s₄,s₃,s₂,w.injective.eq_iff,empty])
      (by simp [Workspace.differenceRoles,differenceSelection,s₄,s₃,s₂,w.injective.eq_iff,empty])
      (by simp [Workspace.differenceRoles,differenceSelection,s₄,s₃,s₂,w.injective.eq_iff,empty])
    simpa [s₅,s₄,s₃,s₂,garbage,Workspace.differenceRoles,differenceSelection,w.injective.eq_iff,empty,mValue] using run
  have f : Executes (centerRoutine (extra+6) w.productRoles) s₅
      (centerCost (garbage n m) (order n m) 0) s₆ := by
    have run := centerRoutine_executes (extra+6) w.productRoles (garbage n m) (order n m) 0 s₅
      (by simp [Workspace.productRoles,productSelection,s₅])
      (by simp [Workspace.productRoles,productSelection,s₅,s₄,w.injective.eq_iff])
      (by simp [Workspace.productRoles,productSelection,s₅,s₄,s₃,s₂,w.injective.eq_iff,empty])
      (by simp [Workspace.productRoles,productSelection,s₅,s₄,s₃,s₂,w.injective.eq_iff,empty])
      (by simp [Workspace.productRoles,productSelection,s₅,s₄,s₃,s₂,w.injective.eq_iff,empty])
      (by simp [Workspace.productRoles,productSelection,s₅,s₄,s₃,s₂,w.injective.eq_iff,empty])
    simpa [s₆,Workspace.productRoles,productSelection] using run
  have g : Executes (scaleLength (extra+9) (w 1) (w 6) (w 10) 3) s₆ (3*(5*m+3)) s₇ := by
    have run := scaleLength_executes (extra+9) (w 1) (w 6) (w 10)
      (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) 3 s₆
      (by simp [s₆,s₅,s₄,s₃,s₂,w.injective.eq_iff,empty])
    simpa [s₇,s₆,s₅,s₄,s₃,s₂,w.injective.eq_iff,empty,mValue] using run
  have h : Executes (scaleLength (extra+9) (w 4) (w 6) (w 10) 1) s₇ (5*order n m+3) s₈ := by
    have run := scaleLength_executes (extra+9) (w 4) (w 6) (w 10)
      (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) 1 s₇
      (by simp [s₇,s₆,s₅,s₄,s₃,s₂,w.injective.eq_iff,empty])
    simpa [s₈,s₇,s₆,s₅,s₄,w.injective.eq_iff,←List.replicate_add] using run
  have last := move_executes (extra+9) (w 8) (w 6) (w 10)
    (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) s₈
    (by simp [s₈,s₆,s₅,s₄,s₃,s₂,w.injective.eq_iff,empty])
  have source : s₈ (w 8)=List.replicate (garbage n m*order n m) true := by simp [s₈,s₆,w.injective.eq_iff]
  have target : s₈ (w 6)=List.replicate (order n m+3*m) true := by simp [s₈]
  rw [source,target,List.length_replicate,←List.replicate_add] at last
  have final : Function.update (Function.update s₈ (w 6)
      (List.replicate (garbage n m*order n m+(order n m+3*m)) true)) (w 8) []=result w n m store := by
    funext r
    by_cases scratch : r=w 8
    · subst r;simp [result,w.injective.eq_iff,empty]
    · by_cases output : r=w 6
      · subst r;simp [scratch,result,edges,Nat.add_comm,Nat.add_assoc]
      · simp [s₈,s₆,s₅,s₄,s₃,s₂,result,scratch,output]
  rw [final] at last
  have combined := a.sequence (b.sequence (c.sequence (d.sequence (e.sequence (f.sequence (g.sequence (h.sequence last)))))))
  convert combined using 1 <;> first
    | rfl
    | (simp only [cost,centerCost,addScaledDifferenceCost,garbage,order,slots]; ring)

theorem cost_polynomial (n m : Nat) : cost n m ≤ 500*(n+m+1)^4 := by
  let D := n+m+1
  have positive : 1 ≤ D := by dsimp [D];omega
  have nd : n ≤ D := by dsimp [D];omega
  have md : m ≤ D := by dsimp [D];omega
  have kd : 3*m+1 ≤ 3*D := by dsimp [D];omega
  have sd : slots n m ≤ 3*D^2 := by
    have h := Nat.mul_le_mul nd kd
    dsimp only [slots]
    nlinarith only [h]
  have qd : order n m ≤ 6*D^2 := by dsimp only [order];omega
  have gd : garbage n m ≤ 3*D^2 := (Nat.sub_le _ _).trans sd
  have pd : garbage n m*order n m ≤ 18*D^4 := by
    have h := Nat.mul_le_mul gd qd
    nlinarith only [h]
  have power2 : D^2 ≤ D^4 := Nat.pow_le_pow_right positive (by decide)
  have power1 : D ≤ D^4 := Nat.le_self_pow (by decide) D
  have power0 : 1 ≤ D^4 := Nat.one_le_pow _ _ positive
  change cost n m ≤ 500*D^4
  dsimp only [cost]
  nlinarith only [sd,qd,gd,pd,nd,md,power2,power1,power0]

theorem routine_executes_polynomial (extra : Nat) (w : Workspace extra) (n m : Nat)
    (store : Fin (extra+12) → List Bool)
    (nValue : store (w 0)=List.replicate n true) (mValue : store (w 1)=List.replicate m true)
    (empty : ∀ i : Fin 12,i≠0 → i≠1 → store (w i)=[]) :
    ∃ time ≤ 500*(n+m+1)^4,Executes (routine extra w) store time (result w n m store) :=
  ⟨cost n m,cost_polynomial n m,routine_executes extra w n m store nValue mValue empty⟩

end Counting.External.MatchingDimensions
