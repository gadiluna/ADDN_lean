import Counting.ExternalCoordinateCenter
import Counting.StackEncodingBranch
import Counting.StackRoutineBasic

namespace Counting.External.MatchingMachine
open StackMachine StackMachine.Routine StackMachine.EncodingPrograms CookLevin.StackGenerator
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

abbrev LiteralPortWorkspace (extra : Nat) := Fin 8 ↪ Fin (extra+8)
def portCenterPositions : Fin 6 ↪ Fin 8 := ⟨![0,1,2,5,6,7],by decide⟩
def LiteralPortWorkspace.center (w : LiteralPortWorkspace extra) : PolynomialWorkspace (extra+2) := portCenterPositions.trans w

def portValue (index width occurrence shift : Nat) (sign : Bool) :=
  (if sign then shift else 0)+index*width+occurrence

def computePort (extra : Nat) (w : LiteralPortWorkspace extra) : Routine (extra+6) :=
  sequence (centerRoutine (extra+2) w.center)
    (branchRoutine (w 4) (ofProgram (ListPrograms.copyProgram (extra+5) (w 3) (w 5) (w 7))) (skip (extra+6)))

def portCost (index width occurrence shift : Nat) (sign : Bool) :=
  centerCost index width occurrence+2+(if sign then 5*shift+2 else 0)

theorem computePort_executes (extra : Nat) (w : LiteralPortWorkspace extra) (store : Fin (extra+8) → List Bool)
    (index width occurrence shift : Nat) (sign : Bool)
    (v0 : store (w 0)=List.replicate index true) (v1 : store (w 1)=List.replicate width true)
    (v2 : store (w 2)=List.replicate occurrence true) (v3 : store (w 3)=List.replicate shift true)
    (flag : store (w 4)=[sign]) (outEmpty : store (w 5)=[]) (counterEmpty : store (w 6)=[]) (workEmpty : store (w 7)=[]) :
    Executes (computePort extra w) store (portCost index width occurrence shift sign)
      (Function.update (Function.update store (w 4) []) (w 5) (List.replicate (portValue index width occurrence shift sign) true)) := by
  have center := centerRoutine_executes (extra+2) w.center index width occurrence store v0 v1 v2 outEmpty counterEmpty workEmpty
  let centered := Function.update store (w 5) (List.replicate (index*width+occurrence) true)
  let cleared := Function.update centered (w 4) []
  let copied := ofProgram (ListPrograms.copyProgram (extra+5) (w 3) (w 5) (w 7))
  have centeredFlag : centered (w 4)=[sign] := by simp [centered,w.injective.eq_iff,flag]
  cases sign with
  | false =>
    have branch := branch_executes_false (w 4) copied (skip (extra+6)) centered cleared [] 0 centeredFlag (skip_executes cleared)
    have composed := center.sequence branch
    have final : cleared=Function.update (Function.update store (w 4) []) (w 5)
        (List.replicate (portValue index width occurrence shift false) true) := by
      funext r
      by_cases o : r=w 5
      · subst r;simp [cleared,centered,w.injective.eq_iff,portValue]
      · simp [cleared,centered,portValue,o,Function.update_apply]
    rw [final] at composed
    simpa [computePort,portCost,copied] using composed
  | true =>
    have copying := copy_executes (extra+5) (w 3) (w 5) (w 7) (by simp [w.injective.eq_iff])
      (by simp [w.injective.eq_iff]) (by simp [w.injective.eq_iff]) cleared
      (by simp [cleared,centered,w.injective.eq_iff,workEmpty])
    have copyAs : Executes copied cleared (5*shift+2)
        (Function.update (Function.update store (w 4) []) (w 5)
          (List.replicate (portValue index width occurrence shift true) true)) := by
      have source : cleared (w 3)=List.replicate shift true := by simp [cleared,centered,w.injective.eq_iff,v3]
      have target : cleared (w 5)=List.replicate (index*width+occurrence) true := by simp [cleared,centered,w.injective.eq_iff]
      rw [source,target,List.length_replicate,←List.replicate_add] at copying
      have final : Function.update cleared (w 5) (List.replicate (shift+(index*width+occurrence)) true)=
          Function.update (Function.update store (w 4) []) (w 5) (List.replicate (portValue index width occurrence shift true) true) := by
        funext r
        by_cases o : r=w 5
        · subst r;simp [portValue,Nat.add_assoc]
        · simp [cleared,centered,o,Function.update_apply]
      rw [final] at copying
      exact copying
    have branch := branch_executes_true (w 4) copied (skip (extra+6)) centered _ [] (5*shift+2) centeredFlag copyAs
    have composed := center.sequence branch
    have cost : centerCost index width occurrence+1+(1+(5*shift+2))=portCost index width occurrence shift true := by
      simp only [portCost,if_true]
      omega
    rw [cost] at composed
    exact composed

theorem portCost_le (index width occurrence shift bound : Nat) (sign : Bool)
    (hi : index ≤ bound) (hw : width ≤ bound) (ho : occurrence ≤ bound) (hs : shift ≤ bound) :
    portCost index width occurrence shift sign ≤ 40*(bound+1)^2 := by
  have center := centerCost_bound index width occurrence bound hi hw ho
  have linear : bound+1 ≤ (bound+1)^2 := Nat.le_self_pow (by decide) _
  cases sign <;> simp only [portCost,Bool.false_eq_true,if_false,if_true] <;> omega

end Counting.External.MatchingMachine
