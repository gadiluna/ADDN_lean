import Counting.StackScaleInPlace

namespace Counting.StackMachine.Routine

def scaleMany (extra : Nat) (temporary work : Fin (extra+3)) (scale : Nat) : List (Fin (extra+3)) → Routine (extra+1)
  | [] => skip (extra+1)
  | target::rest => sequence (scaleMany extra temporary work scale rest)
      (scaleInPlace extra target temporary work scale)

def scaledStore (targets : List (Fin (extra+3))) (scale : Nat) (store : Fin (extra+3) → List Bool) :=
  fun register => if register ∈ targets then List.replicate (scale*(store register).length) true else store register

def scaleManyCost (targets : List (Fin (extra+3))) (scale : Nat) (store : Fin (extra+3) → List Bool) : Nat :=
  (targets.map (fun target => 7*scale*(store target).length+3*scale+(store target).length+5)).sum

theorem scaleMany_executes (extra : Nat) (temporary work : Fin (extra+3)) (scale : Nat)
    (targets : List (Fin (extra+3))) (unique : targets.Nodup)
    (tempOutside : temporary ∉ targets) (workOutside : work ∉ targets) (tw : temporary ≠ work)
    (store : Fin (extra+3) → List Bool) (temporaryEmpty : store temporary=[]) (workEmpty : store work=[]) :
    Executes (scaleMany extra temporary work scale targets) store (scaleManyCost targets scale store)
      (scaledStore targets scale store) := by
  induction targets with
  | nil =>
      have same : scaledStore ([] : List (Fin (extra+3))) scale store=store := by
        funext r
        simp [scaledStore]
      change Executes (skip (extra+1)) store 0 (scaledStore [] scale store)
      rw [same]
      exact skip_executes store
  | cons target rest ih =>
      obtain ⟨notMem,uniqueRest⟩ := List.nodup_cons.mp unique
      have tempRest : temporary ∉ rest := fun h => tempOutside (List.mem_cons_of_mem target h)
      have workRest : work ∉ rest := fun h => workOutside (List.mem_cons_of_mem target h)
      have st : target ≠ temporary := fun same => tempOutside (same ▸ List.mem_cons_self)
      have sw : target ≠ work := fun same => workOutside (same ▸ List.mem_cons_self)
      have earlier := ih uniqueRest tempRest workRest
      have scaled := scaleInPlace_executes extra target temporary work scale st sw tw (scaledStore rest scale store)
        (by simp [scaledStore,tempRest,temporaryEmpty]) (by simp [scaledStore,workRest,workEmpty])
      have targetValue : scaledStore rest scale store target=store target := by simp [scaledStore,notMem]
      have result : Function.update (scaledStore rest scale store) target
          (List.replicate (scale*(store target).length) true)=scaledStore (target::rest) scale store := by
        funext r
        by_cases same : r=target
        · subst r; simp [scaledStore]
        · simp [scaledStore,same]
      rw [targetValue,result] at scaled
      have combined := earlier.sequence scaled
      have cost : scaleManyCost rest scale store+1+(7*scale*(store target).length+3*scale+(store target).length+4)=
          scaleManyCost (target::rest) scale store := by
        simp only [scaleManyCost,List.map_cons,List.sum_cons]
        omega
      simpa only [scaleMany,cost] using combined

theorem scaleManyCost_bound (targets : List (Fin (extra+3))) (scale : Nat) (store : Fin (extra+3) → List Bool)
    (bound : Nat) (bounded : ∀ target ∈ targets, (store target).length≤bound) :
    scaleManyCost targets scale store ≤ targets.length*((7*scale+1)*bound+3*scale+5) := by
  induction targets with
  | nil => simp [scaleManyCost]
  | cons target rest ih =>
      have one := bounded target List.mem_cons_self
      have restBound := ih (fun r h => bounded r (List.mem_cons_of_mem target h))
      have mulBound := Nat.mul_le_mul_left (7*scale) one
      simp only [scaleManyCost,List.map_cons,List.sum_cons,List.length_cons] at *
      nlinarith

end Counting.StackMachine.Routine
