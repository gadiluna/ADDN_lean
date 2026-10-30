import Counting.ExternalInitialPrepare
import Counting.StackScaleMany

namespace Counting.External.CookLevin.StackGenerator
open StackMachine StackMachine.Routine

def initialTargets (w : InitialWorkspace extra) : List (Fin (extra+24)) :=
  [w 6,w 7,w 8,w 9,w 10,w 11,w 12]

theorem initialTargets_unique (w : InitialWorkspace extra) : (initialTargets w).Nodup := by
  simp [initialTargets,w.injective.eq_iff]

theorem initialPrepared_outside (w : InitialWorkspace extra) (store : Fin (extra+24) → List Bool)
    (place offset capacity : Nat) (register : Fin (extra+24)) (outside : register ∉ initialTargets w) :
    initialPrepared w store place offset capacity register=store register := by
  simp only [initialTargets,List.mem_cons,List.not_mem_nil,or_false,not_or] at outside
  rcases outside with ⟨h6,h7,h8,h9,h10,h11,h12⟩
  simp [initialPrepared,h6,h7,h8,h9,h10,h11,h12]

theorem initialPrepared_length (w : InitialWorkspace extra) (store : Fin (extra+24) → List Bool)
    (place offset capacity : Nat) (register : Fin (extra+24)) (member : register ∈ initialTargets w) :
    (initialPrepared w store place offset capacity register).length ≤ place+(store (w 2)).length+capacity+1 := by
  simp only [initialTargets,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp [initialPrepared,w.injective.eq_iff]
  all_goals try omega
  cases (store (w 2))[place-offset]? <;> simp

theorem initial_cleanup (w : InitialWorkspace extra) (store : Fin (extra+24) → List Bool)
    (place offset capacity : Nat) (payload : List Bool)
    (empty : ∀ i ∈ ([6,7,8,9,10,11,12] : List (Fin 24)), store (w i)=[]) :
    scaledStore (initialTargets w) 0
      (Function.update (initialPrepared w store place offset capacity) (w 5) payload)=
      Function.update store (w 5) payload := by
  funext r
  by_cases member : r ∈ initialTargets w
  · have outside : r ≠ w 5 := by
      intro same
      simp [same,initialTargets,w.injective.eq_iff] at member
    have original : store r=[] := by
      simp only [initialTargets,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals apply empty; simp
    simp [scaledStore,member,outside,original]
  · by_cases output : r=w 5
    · subst r; simp [scaledStore,member]
    · simp [scaledStore,member,output,initialPrepared_outside w store place offset capacity r member]

end Counting.External.CookLevin.StackGenerator
